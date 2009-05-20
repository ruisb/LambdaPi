module SimplyTyped.Interpreter where
  import Interpreter.Types
  import Interpreter.Runner
  import SimplyTyped.Types
  import SimplyTyped.Functions
  import SimplyTyped.Parser
  import SimplyTyped.Printer
 
  st :: Interpreter ITerm CTerm Value Type Info Info
  st = I { iname = "the simply typed lambda calculus",
           iprompt = "ST> ",
           iitype = \ v c -> iType 0 c,
           iquote = quote0,
           ieval  = \ e x -> iEval x (e, []),
           ihastype = HasType,
           icprint = cPrint 0 0,
           itprint = tPrint 0,
           iiparse = parseITerm 0 [],
           isparse = parseStmt [],
           iassume = \ s (x, t) -> stassume s x t }
 

 
  repST :: Bool -> IO ()
  repST b = readevalprint st (b, [], [], [])

  stassume state@(inter, out, ve, te) x t = return (inter, out, ve, (Global x, t) : te)

