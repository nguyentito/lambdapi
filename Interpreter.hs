{-# LANGUAGE ScopedTypeVariables #-}

module Interpreter where
-- {-# LINE 152 "LP.lhs" #-}
import Prelude hiding (print)
-- {-# LINE 154 "LP.lhs" #-}
import Control.Monad.Error
import Control.Exception
import Data.List
import Data.Char
-- {-# LINE 159 "LP.lhs" #-}
import Text.PrettyPrint.HughesPJ hiding (parens)
-- {-# LINE 164 "LP.lhs" #-}
import Text.ParserCombinators.Parsec hiding (parse, State)
-- {-# LINE 171 "LP.lhs" #-}
import System.Console.Readline
-- {-# LINE 176 "LP.lhs" #-}

import Term
import LambdaPi
import Parser
import Printer

-- {-# LINE 13 "Interpreter.lhs" #-}
--  read-eval-print loop
readevalprint :: Interpreter i c v t tinf inf -> State v inf -> IO ()
readevalprint int state@(inter, out, ve, te) =
  let rec int state =
        do
          x <- catch
                 (if inter
                  then readline (iprompt int) 
                  else fmap Just getLine)
                 -- changed to use the new exceptions
                 (\(_ :: SomeException) -> return Nothing)
          case x of
            Nothing   ->  return ()
            Just ""   ->  rec int state
            Just x    ->
              do
                when inter (addHistory x)
                c  <- interpretCommand x
                state' <- handleCommand int state c
                maybe (return ()) (rec int) state'
  in
    do
      --  welcome
      when inter $ putStrLn ("Interpreter for " ++ iname int ++ ".\n" ++
                             "Type :? for help.")
      --  enter loop
      rec int state
-- {-# LINE 40 "Interpreter.lhs" #-}
data Command = TypeOf String
             | Compile CompileForm
             | Browse
             | Quit
             | Help
             | Noop

data CompileForm = CompileInteractive  String
                 | CompileFile         String

data InteractiveCommand = Cmd [String] String (String -> Command) String

-- type NameEnv v = [(Name, v)]
type Ctx inf = [(Name, inf)]
type State v inf = (Bool, String, NameEnv v, Ctx inf)

commands :: [InteractiveCommand]
commands
  =  [ Cmd [":type"]        "<expr>"  TypeOf         "print type of expression",
       Cmd [":browse"]      ""        (const Browse) "browse names in scope",
       Cmd [":load"]        "<file>"  (Compile . CompileFile)
                                                     "load program from file",
       Cmd [":quit"]        ""        (const Quit)   "exit interpreter",
       Cmd [":help",":?"]   ""        (const Help)   "display this list of commands" ]

helpTxt :: [InteractiveCommand] -> String
helpTxt cs
  =  "List of commands:  Any command may be abbreviated to :c where\n" ++
     "c is the first character in the full name.\n\n" ++
     "<expr>                  evaluate expression\n" ++
     "let <var> = <expr>      define variable\n" ++
     "assume <var> :: <expr>  assume variable\n\n"
     ++
     unlines (map (\ (Cmd cs a _ d) -> let  ct = concat (intersperse ", " (map (++ if null a then "" else " " ++ a) cs))
                                       in   ct ++ replicate ((24 - length ct) `max` 2) ' ' ++ d) cs)


interpretCommand :: String -> IO Command
interpretCommand x
  =  if isPrefixOf ":" x then
       do  let  (cmd,t')  =  break isSpace x
                t         =  dropWhile isSpace t'
           --  find matching commands
           let  matching  =  filter (\ (Cmd cs _ _ _) -> any (isPrefixOf cmd) cs) commands
           case matching of
             []  ->  do  putStrLn ("Unknown command `" ++ cmd ++ "'. Type :? for help.")
                         return Noop
             [Cmd _ _ f _]
                 ->  do  return (f t)
             x   ->  do  putStrLn ("Ambiguous command, could be " ++ concat (intersperse ", " [ head cs | Cmd cs _ _ _ <- matching ]) ++ ".")
                         return Noop
     else
       return (Compile (CompileInteractive x))

handleCommand :: Interpreter i c v t tinf inf -> State v inf -> Command -> IO (Maybe (State v inf))
handleCommand int state@(inter, out, ve, te) cmd
  =  case cmd of
       Quit   ->  when (not inter) (putStrLn "!@#$^&*") >> return Nothing
       Noop   ->  return (Just state)
       Help   ->  putStr (helpTxt commands) >> return (Just state)
       TypeOf x ->
                  do  x <- parseIO "<interactive>" (iiparse int) x
                      t <- maybe (return Nothing) (iinfer int ve te) x
                      maybe (return ()) (\u -> putStrLn (render (itprint int u))) t
                      return (Just state)
       Browse ->  do  putStr (unlines [ s | Global s <- reverse (nub (map fst te)) ])
                      return (Just state)
       Compile c ->
                  do  state <- case c of
                                 CompileInteractive s -> compilePhrase int state s
                                 CompileFile f        -> compileFile int state f
                      return (Just state)

compileFile :: Interpreter i c v t tinf inf -> State v inf -> String -> IO (State v inf)
compileFile int state@(inter, out, ve, te) f =
  do
    x <- readFile f
    stmts <- parseIO f (many (isparse int)) x
    maybe (return state) (foldM (handleStmt int) state) stmts

compilePhrase :: Interpreter i c v t tinf inf -> State v inf -> String -> IO (State v inf)
compilePhrase int state@(inter, out, ve, te) x =
  do
    x <- parseIO "<interactive>" (isparse int) x
    maybe (return state) (handleStmt int state) x

data Interpreter i c v t tinf inf =
  I { iname :: String,
      iprompt :: String,
      iitype :: NameEnv v -> Ctx inf -> i -> Result t,
      iquote :: v -> c,
      ieval  :: NameEnv v -> i -> v,
      ihastype :: t -> inf,
      icprint :: c -> Doc,
      itprint :: t -> Doc,
      iiparse :: CharParser () i,
      isparse :: CharParser () (Stmt i tinf),
      iassume :: State v inf -> (String, tinf) -> IO (State v inf) }

lp :: Interpreter ITerm CTerm Value Value CTerm Value
lp = I { iname = "lambda-Pi",
         iprompt = "LP> ",
         iitype = \ v c -> iType 0 (v, c),
         iquote = quote0_,
         ieval = \ e x -> iEval_ x (e, []),
         ihastype = id,
         icprint = cPrint_ 0 0,
         itprint = cPrint_ 0 0 . quote0_,
         iiparse = parseITerm 0 [],
         isparse = parseStmt_ [],
         iassume = \ s (x, t) -> lpassume s x t }

lpte :: Ctx Value
lpte =      [(Global "Zero", VNat),
             (Global "Succ", VPi VNat (\ _ -> VNat)),
             (Global "Nat", VStar),
             (Global "natElim", VPi (VPi VNat (\ _ -> VStar)) (\ m ->
                               VPi (m `vapp_` VZero) (\ _ ->
                               VPi (VPi VNat (\ k -> VPi (m `vapp_` k) (\ _ -> (m `vapp_` (VSucc k))))) ( \ _ ->
                               VPi VNat (\ n -> m `vapp_` n))))),
             (Global "Nil", VPi VStar (\ a -> VVec a VZero)),
             (Global "Cons", VPi VStar (\ a ->
                            VPi VNat (\ n ->
                            VPi a (\ _ -> VPi (VVec a n) (\ _ -> VVec a (VSucc n)))))),
             (Global "Vec", VPi VStar (\ _ -> VPi VNat (\ _ -> VStar))),
             (Global "vecElim", VPi VStar (\ a ->
                               VPi (VPi VNat (\ n -> VPi (VVec a n) (\ _ -> VStar))) (\ m ->
                               VPi (m `vapp_` VZero `vapp_` (VNil a)) (\ _ ->
                               VPi (VPi VNat (\ n ->
                                     VPi a (\ x ->
                                     VPi (VVec a n) (\ xs ->
                                     VPi (m `vapp_` n `vapp_` xs) (\ _ ->
                                     m `vapp_` VSucc n `vapp_` VCons a n x xs))))) (\ _ ->
                               VPi VNat (\ n ->
                               VPi (VVec a n) (\ xs -> m `vapp_` n `vapp_` xs))))))),
             (Global "Refl", VPi VStar (\ a -> VPi a (\ x ->
                            VEq a x x))),
             (Global "Eq", VPi VStar (\ a -> VPi a (\ x -> VPi a (\ y -> VStar)))),
             (Global "eqElim", VPi VStar (\ a ->
                              VPi (VPi a (\ x -> VPi a (\ y -> VPi (VEq a x y) (\ _ -> VStar)))) (\ m ->
                              VPi (VPi a (\ x -> m `vapp_` x `vapp_` x `vapp_` VRefl a x)) (\ _ ->
                              VPi a (\ x -> VPi a (\ y ->
                              VPi (VEq a x y) (\ eq ->
                              m `vapp_` x `vapp_` y `vapp_` eq))))))),
             (Global "FZero", VPi VNat (\ n -> VFin (VSucc n))),
             (Global "FSucc", VPi VNat (\ n -> VPi (VFin n) (\ f ->
                             VFin (VSucc n)))),
             (Global "Fin", VPi VNat (\ n -> VStar)),
             (Global "finElim", VPi (VPi VNat (\ n -> VPi (VFin n) (\ _ -> VStar))) (\ m ->
                               VPi (VPi VNat (\ n -> m `vapp_` (VSucc n) `vapp_` (VFZero n))) (\ _ ->
                               VPi (VPi VNat (\ n -> VPi (VFin n) (\ f -> VPi (m `vapp_` n `vapp_` f) (\ _ -> m `vapp_` (VSucc n) `vapp_` (VFSucc n f))))) (\ _ ->
                               VPi VNat (\ n -> VPi (VFin n) (\ f ->
                               m `vapp_` n `vapp_` f))))))]

lpve :: Ctx Value
lpve =      [(Global "Zero", VZero),
             (Global "Succ", VLam (\ n -> VSucc n)),
             (Global "Nat", VNat),
             (Global "natElim", cEval_ (Lam (Lam (Lam (Lam (Inf (NatElim (Inf (Bound 3)) (Inf (Bound 2)) (Inf (Bound 1)) (Inf (Bound 0)))))))) ([], [])),
             (Global "Nil", VLam (\ a -> VNil a)),
             (Global "Cons", VLam (\ a -> VLam (\ n -> VLam (\ x -> VLam (\ xs ->
                            VCons a n x xs))))),
             (Global "Vec", VLam (\ a -> VLam (\ n -> VVec a n))),
             (Global "vecElim", cEval_ (Lam (Lam (Lam (Lam (Lam (Lam (Inf (VecElim (Inf (Bound 5)) (Inf (Bound 4)) (Inf (Bound 3)) (Inf (Bound 2)) (Inf (Bound 1)) (Inf (Bound 0)))))))))) ([],[])),
             (Global "Refl", VLam (\ a -> VLam (\ x -> VRefl a x))),
             (Global "Eq", VLam (\ a -> VLam (\ x -> VLam (\ y -> VEq a x y)))),
             (Global "eqElim", cEval_ (Lam (Lam (Lam (Lam (Lam (Lam (Inf (EqElim (Inf (Bound 5)) (Inf (Bound 4)) (Inf (Bound 3)) (Inf (Bound 2)) (Inf (Bound 1)) (Inf (Bound 0)))))))))) ([],[])),
             (Global "FZero", VLam (\ n -> VFZero n)),
             (Global "FSucc", VLam (\ n -> VLam (\ f -> VFSucc n f))),
             (Global "Fin", VLam (\ n -> VFin n)),
             (Global "finElim", cEval_ (Lam (Lam (Lam (Lam (Lam (Inf (FinElim (Inf (Bound 4)) (Inf (Bound 3)) (Inf (Bound 2)) (Inf (Bound 1)) (Inf (Bound 0))))))))) ([],[]))]
-- {-# LINE 225 "Interpreter.lhs" #-}
repLP :: Bool -> IO ()
repLP b = readevalprint lp (b, [], lpve, lpte)

iinfer int d g t =
  case iitype int d g t of
    Left e -> putStrLn e >> return Nothing
    Right v -> return (Just v)

handleStmt :: Interpreter i c v t tinf inf
              -> State v inf -> Stmt i tinf -> IO (State v inf)
handleStmt int state@(inter, out, ve, te) stmt =
  do
    case stmt of
        Assume ass -> foldM (iassume int) state ass 
        Let x e    -> checkEval x e
        Eval e     -> checkEval it e
        PutStrLn x -> putStrLn x >> return state
        Out f      -> return (inter, f, ve, te)
  where
    --  checkEval :: String -> i -> IO (State v inf)
    checkEval i t =
      check int state i t
        (\ (y, v) -> do
                       --  ugly, but we have limited space in the paper
                       --  usually, you'd want to have the bound identifier *and*
                       --  the result of evaluation
                       let outtext = if i == it then render (icprint int (iquote int v) <> text " :: " <> itprint int y)
                                                else render (text i <> text " :: " <> itprint int y)
                       putStrLn outtext
                       unless (null out) (writeFile out (process outtext)))
        (\ (y, v) -> (inter, "", (Global i, v) : ve, (Global i, ihastype int y) : te))

check :: Interpreter i c v t tinf inf -> State v inf -> String -> i
         -> ((t, v) -> IO ()) -> ((t, v) -> State v inf) -> IO (State v inf)
check int state@(inter, out, ve, te) i t kp k =
                do
                  --  typecheck and evaluate
                  x <- iinfer int ve te t
                  case x of
                    Nothing  ->
                      do
                        --  putStrLn "type error"
                        return state
                    Just y   ->
                      do
                        let v = ieval int ve t
                        kp (y, v)
                        return (k (y, v))

stassume state@(inter, out, ve, te) x t = return (inter, out, ve, (Global x, t) : te)
lpassume state@(inter, out, ve, te) x t =
  check lp state x (Ann t (Inf Star))
        (\ (y, v) -> return ()) --  putStrLn (render (text x <> text " :: " <> cPrint_ 0 0 (quote0_ v))))
        (\ (y, v) -> (inter, out, ve, (Global x, v) : te))


it = "it"
-- {-# LINE 288 "Interpreter.lhs" #-}
process :: String -> String
process = unlines . map (\ x -> "< " ++ x) . lines
-- {-# LINE 293 "Interpreter.lhs" #-}
main :: IO ()
main = repLP True


