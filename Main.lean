import Sexp

def main (args : List String) : IO Unit := do
  let srcDir := args.get! 0
  let outDir := args.get! 1
  IO.println s!"Extracting s-expressions from {srcDir} to {outDir}"

-- def main (args : List String) : IO Unit := do
--   for fileName in args do
--     let (data, _) ← Lean.readModuleData fileName
--     IO.println $ Sexp.fromModuleData (.mkStr3 "fake" "module" "name") data