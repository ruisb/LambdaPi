module Interpreter.Runner where
import Interpreter.Types
import LambdaPi.Parser(parseIO)
import System.Console.Haskeline (getInputLine, runInputT, defaultSettings, InputT)
import System.Console.Haskeline.History (addHistory)

--FIXME temp
import Debug.Trace (trace)

import Data.Char
import Data.List
import Control.Monad.Error
import System.IO hiding (print)
import Text.ParserCombinators.Parsec hiding (parse, State)
import qualified Text.ParserCombinators.Parsec as P
import Text.PrettyPrint.HughesPJ hiding (parens)
import qualified Text.PrettyPrint.HughesPJ as PP
import qualified Data.Map as Map


--  read-eval-print loop
readevalprint :: Interpreter i c v t tinf inf -> State v inf -> IO ()
readevalprint int state@(inter, out, ve, te) =
  let rec int state =
        do
          x <- catch
                 (if inter
                  then readline (iprompt int)
                  else fmap Just getLine)
                 (\_ -> return Nothing)
          case x of
            Nothing   ->  return ()
            Just ""   ->  rec int state
            Just x    ->
              do
                -- when inter (addHistory x) -- FIXME not needed? autoAddHistory is default=true
                -- see http://hackage.haskell.org/packages/archive/haskeline/0.6.1.6/doc/html/System-Console-Haskeline-History.html
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
      
        where
        readline :: String -> IO (Maybe String)
        readline s = runInputT defaultSettings $ loop s

        loop :: String -> InputT IO (Maybe String)
        loop s = getInputLine s
            


data Command = TypeOf String
             | Compile CompileForm
             | Browse
             | Quit
             | Help
             | Noop -- No operation

-- The source where to compile from.
data CompileForm = CompileInteractive  String
                 | CompileFile         String

data InteractiveCommand = Cmd [String] String (String -> Command) String


commands :: [InteractiveCommand]
commands
  =  [ Cmd [":type"]        "<expr>"  TypeOf         "print type of expression",
       Cmd [":browse"]      ""        (const Browse) "browse names in scope",
       Cmd [":load"]        "<file>"  (Compile . CompileFile)
                                                     "load program from file",
       Cmd [":quit"]        ""        (const Quit)   "exit interpreter",
       Cmd [":help",":?"]   ""        (const Help)   "display this list of commands" ]

-- The help text.
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

-- Handle a command that the user has given (Quit, Browse etc.)
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
       Browse ->  do  putStr (unlines (reverse (nub (map fst te)) )) -- show the names from the context of the state
                      return (Just state)
       Compile c ->
                  do  state <- case c of
                                 CompileInteractive s -> compilePhrase int state s
                                 CompileFile f        -> compileFile int state f
                      return (Just state)

-- Compile a file
compileFile :: Interpreter i c v t tinf inf -> State v inf -> FilePath -> IO (State v inf)
compileFile int state@(inter, out, ve, te) f =
  do
    x <- readFile (reverse . dropWhile isSpace . reverse $ f)
    stmts <- parseIO f (many (isparse int)) x
    maybe (return state) (foldM (handleStmt int) state) stmts

-- Compile from command line.
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
      iassume :: State v inf -> (String, tinf) -> IO (State v inf),
      iprcdata :: DataInfo tinf -> State v inf -> Result (State v inf) }

iinfer int d g t =
  case iitype int d g t of
    Left e -> putStrLn e >> return Nothing
    Right v -> return (Just v)

-- Handle a statement that is parsed.
handleStmt :: Interpreter i c v t tinf inf ->
              State v inf -> Stmt i tinf -> IO (State v inf)
handleStmt int state@(inter, out, ve, te) stmt =
  do
    case stmt of
        Assume ass -> foldM (iassume int) state ass 
        Let x e    -> checkEval x e
        Eval e     -> checkEval it e
        PutStrLn x -> putStrLn x >> return state
        Out f      -> return (inter, f, ve, te)
        DataDecl datainfo -> trace ( "found Datatype " ++ name datainfo ++ " with "
         -- ++ " ,type: "     ++ printI t
         -- ++ " ,mappings:"  ++ (Map.showTreeWith (\k a -> show k ++ "[" ++ printI a ++ "]," ) True True m)) -- FIXME remove trace
          ++ (show . length . ctors $datainfo) ++ " constructors.")
         -- (return ((name, t) : te)) -- add to typing env.
         --(return (inter, out, ve, (name, (iitype int) ve te t ) : te))
           $ reportresult state $ iprcdata int datainfo state
        -- FIXME
    where
    --FIXME temp
    printI = PP.render . icprint int . iquote int . (ieval int) ve
    reportresult :: a -> Result a -> IO a 
    reportresult x (Left  err) = putStrLn ("error: \n" ++ err) >> return x
    reportresult _ (Right res) = return res
    
    --  checkEval :: String -> i -> IO (State v inf)
    checkEval i t =
      check int state i t
        (\ (y, v) -> do
                       -- FIXME limited space thing?
                       --  ugly, but we have limited space in the paper
                       --  usually, you'd want to have the bound identifier *and*
                       --  the result of evaluation
                       let outtext = if i == it then render (icprint int (iquote int v) <> text " :: " <> itprint int y)
                                                else render (text i <> text " :: " <> itprint int y)
                       putStrLn outtext
                       unless (null out) (writeFile out (process outtext)))
        (\ (y, v) -> (inter, "", (i, v) : ve, (i, ihastype int y) : te))

check :: Interpreter i c v t tinf inf -> State v inf -> String -> i
         -> ((t, v) -> IO ()) -> ((t, v) -> State v inf) -> IO (State v inf)
check int state@(inter, out, ve, te) i t kp k =
                do
                  --  typecheck and evaluate
                  x <- iinfer int ve te t
                  case x of
                    Nothing  ->
                      do
                        --  putStrLn "type error" -- FIXME old?
                        return state
                    Just y   ->
                      do
                        let v = ieval int ve t
                        kp (y, v)
                        return (k (y, v))

-- FIXME wherefore this it? (it's used at checkEval function)
it = "it"

process :: String -> String
process = unlines . map (\ x -> "< " ++ x) . lines
