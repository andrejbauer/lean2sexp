import Lean
import Sexp
import Tree.Bird

structure Config : Type where
  srcDir : System.FilePath := "build/lib" -- the directory where .olean files are found
  outDir : System.FilePath := "sexp" -- the output directory (created if needed)
  referencesOnly : Bool := False -- only output references names
  force : Bool := False -- process file even if .sexp is newer than .olean

def usage : String :=
"Usage: lake exe lean2sexp <options>

  --srcdir ⟨DIR⟩    set the source directory where .olean files are (default: build/lib)
  --outdir ⟨DIR⟩    set the output directory (default: sexp)
  --referencesOnly  output only referenced names instead of syntax trees, much faster (default: false)
  --force           process a file even if .sexp is newer than .olean (default: false)
"
-- Poor man's parsing of command-line arguments
def parseArgs (conf : Config) (args : List String) : Option Config :=
  match args with
  | [] => .some conf
  | "--srcdir" :: dir :: args => parseArgs {conf with srcDir := dir} args
  | "--outdir" :: dir :: args => parseArgs {conf with srcDir := dir} args
  | "--referencesOnly" :: args => parseArgs {conf with referencesOnly := True} args
  | "--force" :: args => parseArgs {conf with force := True} args
  | _ => .none

unsafe def main (args : List String) : IO Unit := do
  match parseArgs ({} : Config) args with
  | .none =>
    IO.println s!"Error: could not parse command-line arguments\n\n{usage}"
  | .some conf =>
    IO.println s!"Extracting s-expressions from {conf.srcDir} to {conf.outDir}"
    IO.FS.createDirAll conf.outDir
    let allFiles ← System.FilePath.walkDir conf.srcDir
    let files := allFiles.toList.filter (fun fp => fp.toString.endsWith ".olean")
    let totalFiles := files.length
    for (k, srcFile) in files.enumFrom 1 do
      if ! srcFile.toString.startsWith conf.srcDir.toString then
        IO.println s!"skipping {srcFile} because, mysteriously, is not in {conf.outDir}"
      else
        let baseName := (srcFile.withExtension "").components.drop (conf.srcDir.components.length)
        let outFile := System.FilePath.join conf.outDir $ (".".intercalate (baseName ++ ["sexp"]))
        let srcMetadata ← srcFile.metadata
        let outMetadata ← outFile.metadata.toBaseIO 
        let srcNewer : Bool :=
          match outMetadata with
          | .error _ => true
          | .ok m => decide (srcMetadata.modified > m.modified)
        if ! conf.force && ! srcNewer then
          IO.println s!"[{k}/{totalFiles}] SKIPPING {srcFile}"
        else
          IO.println s!"[{k}/{totalFiles}] PROCESSING {srcFile} → {outFile}"
          let (data, region) ← Lean.readModuleData srcFile
          let moduleName := baseName.foldl Lean.Name.str Lean.Name.anonymous
          IO.FS.withFile outFile .write (fun fh => Sexp.write fh $ Sexp.fromModuleData moduleName data)
          region.free
