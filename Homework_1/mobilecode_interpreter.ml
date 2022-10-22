(**@environment*)

type ide = string;;

type 'v t = (string * 'v ) list 

let bind (env:'v t) (x, v) = (x,v)::env;;

let rec lookup (env:'v t) x = 
  match env with 
    | [] -> failwith "Not found"
    | (ide, value)::r -> if x = ide then value else lookup r x;;


(**@permission*)

type perm = Write | NoWrite | Read | NoRead | Send | NoSend | Exe


(*Permission stack*)
type pStack = perm list;;

(**Check if there is an active permission in the trusted environment that is in conflict with 
  the permission p, return true in case of security violation*)
let seekNoP (trustEnv : pStack) (p : perm) : bool =
  if (List.mem Exe trustEnv) then 
      begin match p with
        | Write -> List.mem NoWrite trustEnv       
        | Send -> List.mem NoSend trustEnv
        | Read -> List.mem NoRead trustEnv
        | NoWrite -> List.mem Write trustEnv
        | NoSend -> List.mem Send trustEnv
        | NoRead -> List.mem Read trustEnv
        | Exe -> false
      end
  else false
  
(**Recursive function, given a list of permission check for each permission if is in conflict
  with the permission stack
*)
let rec reCheck (trustEnv : pStack) (l: perm list) : bool = 
  match trustEnv with 
  | [] -> false
  | h::t -> match l with
            |[] -> false
            | c::p -> if(seekNoP trustEnv c)
                      then true
                        else reCheck trustEnv p
                        
(**Given a list of permission return true if one of them is conflict with the permission stack*)
let checkPerm (trustEnv : pStack) (l: perm list) : bool =
    not (reCheck trustEnv l)
  
(**@ast*)

type binop = Sum | Times | Minus | Equal | Less | Greater

type exp = Eint of int
         | Ebool of bool
         | Den of ide 
         | Binop of binop*exp*exp
         | If of exp*exp*exp
         | Let of ide*exp*exp
         | Fun of ide * exp
         | Call of exp*exp
(**@mobilecode*)
         | LocalCode of exp * (perm list)
         | Execute of exp
         | Read of exp
         | Write of exp
         | Send of exp
;;


type  value = Int of int 
            | Bool of bool
            | Closure of  (ide*exp*value t)



(**@interpreter*)

let rec eval env (trustEnv : pStack) (expr:exp)  = 
match expr with 

  |Eint(n) -> Int n
  |Ebool b -> Bool b
  |Den x -> x |> lookup env 

  |If(e1,e2,e3) -> 
                  let guard= eval env trustEnv e1  in
                  begin
                      match guard with
                        | Bool true -> eval env trustEnv e3 
                        | Bool false -> eval env trustEnv e2
                        | _ -> failwith "guard must be boolean"
                  end


  |Let(id, e1, e2) -> let let_value = eval env trustEnv e1  in
                        let new_env = bind env (id,let_value) in
                          eval new_env trustEnv e2


  |Binop(op,e1,e2) -> (let e1 = eval env trustEnv e1  in 
                        let e2 = eval env trustEnv e2 in
                          match op,e1,e2 with 
                            | Sum,Int n1, Int n2 -> Int (n1+n2)
                            | Times,Int n1, Int n2 -> Int (n1 * n2)
                            | Minus,Int n1, Int n2 -> Int (n1-n2)
                            | Equal, Int n1, Int n2 -> Bool (n1 = n2)
                            | Less, Int n1, Int n2 -> Bool (n1 < n2)
                            | Greater, Int n1, Int n2 -> Bool (n1 > n2)
                            | _ -> failwith "Invalid binary expression")  

  |Fun(x, body) -> Closure(x,body,env)

  | Call(func,func_arg)->let closure_f = eval env trustEnv func  in
                            begin
                            match closure_f with
                              | Closure(f_name,f_body,f_env) ->
                                let closure_val= eval env trustEnv func_arg  in
                                  let env1= bind f_env (f_name,closure_val) in
                                    eval env1 trustEnv f_body
                              | _-> failwith "You are not calling a proper function."
                             end

(**@mobilecode*)
(**Each expression that refers to LocalCode or to Network based operation adds permission on the function
permission stack and check if there is a conflict. If so, terminate the execution. *)
  

  | Execute(e) -> 
    let newTEnv = trustEnv @ [Exe] in
    eval env newTEnv e
    
  |LocalCode(e, pList) ->  
              let newTEnv = trustEnv @ pList in
                let guard = (checkPerm newTEnv pList) in 
                  begin
                    match guard with
                  | true -> eval env trustEnv e
                  | false -> failwith "Invalid execution of mobile code: access to local data denied"
                  end


  | Read  e ->
                let  newTEnv = trustEnv @ [Read] in
                  let guard = (checkPerm newTEnv [Read]) in
                    begin
                      match guard with
                    | true -> eval env newTEnv e
                    | false -> failwith "Invalid execution of mobile code: access to local data denied"
                    end
  
  | Write  e -> 
              let newTEnv = trustEnv @ [Write] in
                let guard = (checkPerm newTEnv [Write]) in
                 begin
                  match guard with
                  | true -> eval env newTEnv e
                  | false -> failwith "Invalid execution of mobile code: access to local data denied"
                  end

  | Send  e -> 
              let newTEnv = trustEnv @ [Send] in
                let guard = (checkPerm newTEnv [Send]) in
                 begin
                  match guard with
                  | true -> eval env newTEnv e
                  | false -> failwith "Invalid execution of mobile code: access to local data denied"
                 end


(**@main*)

(*simple tests of the functional programming language*)

let env0 = [];;

let envT = [];;

let e1 = Call(Fun("y", Binop(Sum, Den "y", Eint 1)), Eint 0);;
eval env0 envT e1;;

let e2 = Call(Fun("y", Binop (Sum, Eint 1, Den "y")), Eint 1);;
eval env0 envT e2;;

let e3 = Call(Let("x", Eint 2, Fun("y", Binop(Sum, Den "y", Den "x"))), Eint 1);;
eval env0 envT e3;;

let e4 = Call(Fun("x", If (Binop(Equal ,Den "x", Eint 1), Binop(Sum, Den "x",Eint 2), Binop(Sum,Den "x", Eint 3))),Eint 1);;
eval env0 envT e4;;
  
let myPin = Eint 12345;;
let myRealPin = LocalCode(Eint 58397, [NoWrite;NoSend;NoRead]);;
let myAge = LocalCode(Eint 23, [NoWrite]);;
let myCiao = LocalCode(Eint 1,[NoSend]);;



(*Positive tests*)
let env0 = [];;
let envT = [];;

let t0 = Execute(Call(Fun("z",Binop(Sum, Den "z", Eint 4)), Eint 0));;
let t1 = Execute(Write(myPin));;
let t2 = Execute(let result = myPin in Send(result));;
let t3 = Execute(let result = myAge in Send(Read(result)));;
let t4 = Execute(Execute(Send(myAge)));;
let t5 = Send(myRealPin);;


eval env0 envT t0;; 
eval env0 envT t1;;
eval env0 envT t2;;
eval env0 envT t3;;
eval env0 envT t4;;
eval env0 envT t5;;


(*negative tests
   has to be evaluated only one per time cause the evaluation of
   one of these test will result in a failwith that cause the programs to stop*)
let x0 = Execute(Send(myRealPin));;
let x1 = Execute(Write(myRealPin));;
let x2 = Execute(let result = myAge in Write(result));;
let x3 = Execute(let result = myAge in Read(Write(result)));;
let x4 = Execute(Execute(Send(myRealPin)));;


(* eval env0 envT x0;; 
eval env0 envT x1;;
eval env0 envT x2;; 
eval env0 envT x3;; 
eval env0 envT x4;; *)


