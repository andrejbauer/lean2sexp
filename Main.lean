import Lean
import Sexp

unsafe def main (args : List String) : IO Unit := do
  let srcDir := System.FilePath.mk $ (args.get? 0).getD "build/lib"
  let outDir := System.FilePath.mk $ (args.get? 1).getD "sexp"
  IO.println s!"Extracting s-expressions from {srcDir} to {outDir}"
  IO.FS.createDirAll outDir
  let allFiles ← System.FilePath.walkDir srcDir
  let files := allFiles.toList.filter (fun fp => fp.toString.endsWith ".olean")
  let totalFiles := files.length
  for (k, srcFile) in files.enumFrom 1 do
    if ! srcFile.toString.startsWith srcDir.toString then
      IO.println s!"skipping {srcFile} because, mysteriously, is not in {outDir}"
    else
      let baseName := srcFile.toString.drop (1 + srcDir.toString.length)
      match srcFile.fileStem with
      | .none => IO.println s!"skipping {srcFile} because, mysteriously, has no file extension"
      | .some stemFile =>
        let baseFile := System.FilePath.mk $ baseName.replace "/" "."
        let outFile := System.FilePath.join outDir (baseFile.withExtension "sexp")
        IO.println s!"[{k}/{totalFiles}] {srcFile} -> {outFile}"
        let (data, region) ← Lean.readModuleData srcFile
        let moduleName := (stemFile.splitOn "/").foldl Lean.Name.str Lean.Name.anonymous
        IO.FS.writeFile outFile $ toString $ Sexp.fromModuleData moduleName data
        region.free
