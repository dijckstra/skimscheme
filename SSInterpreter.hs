{-

A basic interpreter for a purely functional subset of Scheme named SkimScheme.
Part of this interpreter has been derived from the "Write Yourself a Scheme in
48 Hours - An Introduction to Haskell through Example", by Jonathan Tang. It
does not implement a number of Scheme's constructs. Moreover, it uses a
different approach to implement mutable state within the language.

The name "SkimScheme" refers to the stripped down nature of this interpreter.
According to the New Oxford American Dictionary, "skim" can mean:

(as a verb) ... read (something) quickly or cursorily so as to note only
the important points.

(as a noun) ... an act of reading something quickly or superficially. 

"skimmed/skim milk" is milk from which the cream has been removed. 

The name emphasizes that we do not want to cover the entire standard, small as
it may be. Instead, we want to focus on some of the important aspects, taking a
language implementer's point of view, with the goal of using it as a teaching
tool. Many, many, many aspects of Scheme standards are not covered (it does not
even support recursion!).

Written by Fernando Castor
Started at: August 28th 2012
Last update: December 17th 2012

-}

module Main where
import System.Environment
import Control.Monad
import Data.Map as Map
import LispVal
import SSParser
import SSPrettyPrinter

-----------------------------------------------------------
--                      INTERPRETER                      --
-----------------------------------------------------------
eval :: StateT -> LispVal -> StateTransformer LispVal
eval env val@(String _) = return val
eval env val@(Atom var) = stateLookup env var 
eval env val@(Number _) = return val
eval env val@(Bool _) = return val
eval env (List [Atom "quote", val]) = return val
eval env (List (Atom "begin":[v])) = eval env v
eval env (List (Atom "begin": l: ls)) = (eval env l) >>= (\v -> case v of { (error@(Error _)) -> return error; otherwise -> eval env (List (Atom "begin": ls))})
eval env (List (Atom "begin":[])) = return (List [])
eval env (List (Atom "if":test:conseq:alt:[])) =
 (eval env test) >>= (\v -> case v of
  (error@(Error _)) -> return error
  (Bool False) -> eval env alt
  otherwise -> eval env conseq
  )
eval env (List (Atom "if":test:conseq:[])) =
 (eval env test) >>= (\v -> case v of
  (error@(Error _)) -> return error
  (Bool False) -> return (List [])
  otherwise -> eval env conseq
  )
eval env (List (Atom "set!":(Atom var):form:[])) = 
  (stateLookup env var) >>= (\v -> case v of
    (error@(Error _)) -> return error
    otherwise -> defineVar env var form)

eval env (List (Atom "let":(List args):expr:[])) = ST $
  (\st -> 
    let curr = union env st -- Saves the env environment into the input environment
        extended = addLet curr env args -- Adds the let definitions from curr into env
        (ST f) = eval extended expr -- Evaluates the let expression
        (result, newState) = f st -- Applies the state transformer to the input environment
        afterState = union (difference newState extended) curr -- Removes the let definitions from the transformed state, and saves it to the curr environment
    in (result, afterState)
    )
eval env lam@(List (Atom "lambda":(List formals):body:[])) = return lam
-- The following line is slightly more complex because we are addressing the
-- case where define is redefined by the user (whatever is the user's reason
-- for doing so. The problem is that redefining define does not have
-- the same semantics as redefining other functions, since define is not
-- stored as a regular function because of its return type.
eval env (List (Atom "define": args)) = maybe (define env args) (\v -> return v) (Map.lookup "define" env)
eval env (List (Atom func : args)) = mapM (eval env) args >>= apply env func
eval env (Error s)  = return (Error s)
eval env form = return (Error ("Could not eval the special form: " ++ (show form)))

stateLookup :: StateT -> String -> StateTransformer LispVal
stateLookup env var = ST $ 
  (\s -> 
    (maybe (Error "variable does not exist.")
      -- This needed to be switched because union joins the first environment into the second,
      -- which meant global variables from env would come first, then the local ones.
      -- The lookup would then find the global variable first and use it.
           id (Map.lookup var (union env s)
    ), s))

-- Because of monad complications, define is a separate function that is not
-- included in the state of the program. This saves us from having to make
-- every predefined function return a StateTransformer, which would also
-- complicate state management. The same principle applies to set!. We are still
-- not talking about local definitions. That's a completely different
-- beast.
define :: StateT -> [LispVal] -> StateTransformer LispVal
define env [(Atom id), val] = defineVar env id val
define env [(List [Atom id]), val] = defineVar env id val
-- This creates lambdas from function definitions.
define env ((List (Atom id:args)):body:[]) = defineVar env id (List [Atom "lambda", (List args), body])
-- define env [(List l), val]
define env args = return (Error "wrong number of arguments")

defineVar env id val = 
  ST (\s -> let (ST f) = eval env val
                (result, newState) = f s
            in (result, (insert id result newState))
     )

-- The maybe function yields a value of type b if the evaluation of 
-- its third argument yields Nothing. In case it yields Just x, maybe
-- applies its second argument f to x and yields (f x) as its result.
-- maybe :: b -> (a -> b) -> Maybe a -> b
apply :: StateT -> String -> [LispVal] -> StateTransformer LispVal
apply env func args =  
                  case (Map.lookup func env) of
                      Just (Native f)  -> return (f args)
                      otherwise -> 
                        (stateLookup env func >>= \res -> 
                          case res of 
                            List (Atom "lambda" : List formals : body : l) -> lambda env formals body args
                            otherwise -> return (Error $ func ++ " not a function.")
                        )
 
-- The lambda function is an auxiliary function responsible for
-- applying user-defined functions, instead of native ones. We use a very stupid 
-- kind of dynamic variable (parameter) scoping that does not even support
-- recursion. This has to be fixed in the project.
lambda :: StateT -> [LispVal] -> LispVal -> [LispVal] -> StateTransformer LispVal
lambda env formals body args = 
  let dynEnv = Prelude.foldr (\(Atom f, a) m -> Map.insert f a m) env (zip formals args)
  in  eval dynEnv body

addLet :: StateT -> StateT -> [LispVal] -> StateT
addLet curr env ((List ((Atom id):val:[]):[])) = insert id (unpackVal (eval curr val) curr) env
addLet curr env ((List ((Atom id):val:[]):ls)) = addLet curr (insert id (unpackVal (eval curr val) curr) env) ls

unpackVal :: StateTransformer LispVal -> StateT -> LispVal
unpackVal (ST f) env = fst (f env)

-- Initial environment of the programs. Maps identifiers to values. 
-- Initially, maps function names to function values, but there's 
-- nothing stopping it from storing general values (e.g., well-known
-- constants, such as pi). The initial environment includes all the 
-- functions that are available for programmers.
environment :: Map String LispVal
environment =   
            insert "number?"        (Native predNumber)
          $ insert "boolean?"       (Native predBoolean)
          $ insert "list?"          (Native predList)
          $ insert "+"              (Native numericSum) 
          $ insert "*"              (Native numericMult)
          $ insert "-"              (Native numericSub)
          $ insert "cons"           (Native cons)
          $ insert "lt?"            (Native numBoolLessThan)
          $ insert "/"              (Native numericDiv)
          $ insert "%"              (Native numericMod)
          $ insert "eqv?"           (Native eqv)
          $ insert "car"            (Native car)
          $ insert "cdr"            (Native cdr)
          $ insert "comment"        (Native comment)
            empty

type StateT = Map String LispVal

-- StateTransformer is a data type that embodies computations
-- that transform the state of the interpreter (add new (String, LispVal)
-- pairs to the state variable). The ST constructor receives a function
-- because a StateTransformer gets the previous state of the interpreter 
-- and, based on that state, performs a computation that might yield a modified
-- state (a modification of the previous one). 
data StateTransformer t = ST (StateT -> (t, StateT))

instance Monad StateTransformer where
  return x = ST (\s -> (x, s))
  (>>=) (ST m) f = ST (\s -> let (v, newS) = m s
                                 (ST resF) = f v
                             in  resF newS
                      )
    
-----------------------------------------------------------
--          HARDWIRED PREDEFINED LISP FUNCTIONS          --
-----------------------------------------------------------

-- Includes some auxiliary functions. Does not include functions that modify
-- state. These functions, such as define and set!, must run within the
-- StateTransformer monad.

comment :: [LispVal] -> LispVal
comment _ = List []

car :: [LispVal] -> LispVal
car [List (a:as)] = a
car [DottedList (a:as) _] = a
car ls = Error "invalid list."

cdr :: [LispVal] -> LispVal
cdr (List (a:as) : ls) = List as
cdr (DottedList (a:[]) c : ls) = c
cdr (DottedList (a:as) c : ls) = DottedList as c
cdr ls = Error "invalid list."

predNumber :: [LispVal] -> LispVal
predNumber (Number _ : []) = Bool True
predNumber (a:[]) = Bool False
predNumber ls = Error "wrong number of arguments."

predBoolean :: [LispVal] -> LispVal
predBoolean (Bool _ : []) = Bool True
predBoolean (a:[]) = Bool False
predBoolean ls = Error "wrong number of arguments."

predList :: [LispVal] -> LispVal
predList (List _ : []) = Bool True
predList (a:[]) = Bool False
predList ls = Error "wrong number of arguments."

numericSum :: [LispVal] -> LispVal
numericSum [] = Number 0
numericSum l = numericBinOp (+) l

numericMult :: [LispVal] -> LispVal
numericMult [] = Number 1
numericMult l = numericBinOp (*) l

numericSub :: [LispVal] -> LispVal
numericSub [] = Error "wrong number of arguments."
-- The following case handles negative number literals.
numericSub [x] = if onlyNumbers [x]
                 then (\num -> (Number (- num))) (unpackNum x)
                 else Error "not a number."
numericSub l = numericBinOp (-) l

cons :: [LispVal] -> LispVal
cons (a:(List as):[]) =  List (a:as)
cons (a:(DottedList as v):[]) = DottedList (a:as) v
cons _ = Error "invalid list."

numBoolLessThan :: [LispVal] -> LispVal
numBoolLessThan l = if onlyNumbers l
                    then lessThan l
                    else Error "not a number."

numericDiv :: [LispVal] -> LispVal
numericDiv [] = Error "wrong number of arguments."
numericDiv [x] = Number (div 1 (unpackNum x))
numericDiv l =  if hasZeroes l
                then Error "division by zero."
                else numericBinOp (div) l

numericMod :: [LispVal] -> LispVal
numericMod [] = Error "wrong number of arguments."
numericMod [x] = Error "wrong number of arguments."
numericMod l = if hasZeroes l then Error "division by zero."
                  else numericBinOp (mod) l

eqv :: [LispVal] -> LispVal
eqv ((Atom a):(Atom b):[]) = Bool (a == b)
eqv ((List []):(List []):[]) = Bool True
eqv ((List (a:as)):(List (b:bs)):[]) = Bool (unpackBool (eqv [a, b]) && unpackBool (eqv [(List as), (List bs)]))
-- DottedList = (List LispVal) LispVal
eqv ((DottedList a as):(DottedList b bs):[]) = Bool (unpackBool (eqv [(List a), (List b)]) && unpackBool (eqv [as, bs]))
eqv ((Number a):(Number b):[]) = Bool (a == b)
eqv ((String a):(String b):[]) = Bool (a == b)
eqv ((Bool a):(Bool b):[]) = Bool (a == b)
eqv ((_):(_):[]) = Bool False
eqv _ = Error "too few arguments." 

numericBinOp :: (Integer -> Integer -> Integer) -> [LispVal] -> LispVal
numericBinOp op args = if onlyNumbers args 
                       then Number $ foldl1 op $ Prelude.map unpackNum args 
                       else Error "not a number."

lessThan :: [LispVal] -> LispVal
lessThan (Number a:Number b:[]) = Bool (a < b)
lessThan (Number a:Number b:ls) = Error "too many arguments."
lessThan _ = Error "too few arguments."
                       
onlyNumbers :: [LispVal] -> Bool
onlyNumbers [] = True
onlyNumbers (Number n:ns) = onlyNumbers ns
onlyNumbers ns = False

hasZeroes :: [LispVal] -> Bool
hasZeroes [] = False
hasZeroes (Number n:ns) = (n == 0) || (hasZeroes ns)    
                       
unpackNum :: LispVal -> Integer
unpackNum (Number n) = n

unpackBool :: LispVal -> Bool
unpackBool (Bool n) = n

-----------------------------------------------------------
--                     main FUNCTION                     --
-----------------------------------------------------------

showResult :: (LispVal, StateT) -> String
showResult (val, defs) = show val ++ "\n" ++ show (toList defs) ++ "\n"

getResult :: StateTransformer LispVal -> (LispVal, StateT)
getResult (ST f) = f empty -- we start with an empty state. 

main :: IO ()
main = do args <- getArgs
          putStr $ showResult $ getResult $ eval environment $ readExpr $ concat $ args 