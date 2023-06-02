import Lean
import Sexp

def main (args : List String) : IO Unit := do
  let srcDir := System.FilePath.mk (args.get! 0)
  let outDir := System.FilePath.mk (args.get! 1)
  IO.println s!"Extracting s-expressions from {srcDir} to {outDir}"
  IO.FS.createDirAll outDir
  let files ← System.FilePath.walkDir srcDir
  --  (fun fp => do { let b ← fp.isDir ; pure $ (b || fp.toString.endsWith ".olean") })
  for srcFile in files.filter (fun fp => fp.toString.endsWith ".olean") do
    if ! srcFile.toString.startsWith srcDir.toString then
      IO.println s!"skipping {srcFile} because, mysteriously, is not in {outDir}"
    else
      let baseName := srcFile.toString.drop (1 + srcDir.toString.length)
      match srcFile.fileStem with
      | .none => IO.println s!"skipping {srcFile} because, mysteriously, has no file extension"
      | .some stemFile =>
        let baseFile := System.FilePath.mk $ baseName.replace "/" "."
        let outFile := System.FilePath.join outDir (baseFile.withExtension "sexp")
        IO.println s!"{srcFile} -> {outFile}"
        let (data, _) ← Lean.readModuleData srcFile
        let moduleName := (stemFile.splitOn "/").foldl Lean.Name.str Lean.Name.anonymous
        IO.FS.writeFile outFile $ toString $ Sexp.fromModuleData moduleName data
