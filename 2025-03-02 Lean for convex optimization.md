
# 2025/03/04 adding dependency `mathlib`
- instructions say "add this to your lakefile.toml" - https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency#in-an-existing-project:
	```toml
	[[require]]
	name = "mathlib"
	scope = "leanprover-community"
	```
- -> ❌ `lake build` fails, `lake update` fails with:
	```
	**warning:** toolchain not updated; multiple toolchain candidates:
	
	  leanprover/lean4:4.16.0
	
	    from «cvx-opt»
	
	  leanprover/lean4:v4.18.0-rc1
	
	    from mathlib
	
	**info:** mathlib: running post-update hooks
	
	**✖ [3/12] Building Cache.IO**
	
	**trace:** .> LEAN_PATH=././.lake/packages/Cli/.lake/build/lib:././.lake/packages/batteries/.lake/build/lib:././.lake/packages/Qq/.lake/build/lib:././.lake/packages/aesop/.lake/build/lib:././.lake/packages/proofwidgets/.lake/build/lib:././.lake/packages/importGraph/.lake/build/lib:././.lake/packages/LeanSearchClient/.lake/build/lib:././.lake/packages/plausible/.lake/build/lib:././.lake/packages/mathlib/.lake/build/lib:././.lake/build/lib DYLD_LIBRARY_PATH= /nix/store/72i4gnyvfwlrjdgn22qmyy29331akygf-lean4-4.16.0/bin/lean ././.lake/packages/mathlib/././Cache/IO.lean -R ././.lake/packages/mathlib/./. -o ././.lake/packages/mathlib/.lake/build/lib/Cache/IO.olean -i ././.lake/packages/mathlib/.lake/build/lib/Cache/IO.ilean -c ././.lake/packages/mathlib/.lake/build/ir/Cache/IO.c --json
	
	**error:** ././.lake/packages/mathlib/././Cache/IO.lean:7:0: object file '././.lake/packages/proofwidgets/.lake/build/lib/Lean/Util/Paths.olean' of module Lean.Util.Paths does not exist
	
	**error:** Lean exited with code 1
	
	Some required builds logged failures:
	
	- Cache.IO
	
	**error:** build failed
	```
- <- maybe set version via this?: https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency#dealing-with-breakages-from-updating
	- `lake build` -> ❌ more errors
	- <- run `lake clean` first, `lake update` & ignore errors
	- `lake build` -> ✅ LOOOONG build time, but succeeded
# 2025/03/04 using LSP in Sublime?
- LSP is allegedly built into the compiler (tbh this makes a lot of sense from a design standpoint, ty devs) - https://lean-lang.org/lean4/doc/setup.html#editing

couple things:
- syntax is set to the label "Lean4" -> have to specify in the LSP settings `"selector": "source.lean4"`, not `source.lean`
	- i.e., it follows the syntax name, not the file extension
- the LSP program is triggered with `lean --server` -> need to specify that flag

-> altogether, `LSP.sublime-settings`:
```json
{
	"clients":
        "lean4": {
            "command": ["/Users/beckerawqatty/.nix-profile/bin/lean", "--server"],
            "enabled": true,
            "selector": "source.lean4",
        },
	},
}
```
# 2025/03/04 `lake build` fails?
error:
```
**✖ [8/8] Building «cvx-opt»**

**trace:** .> MACOSX_DEPLOYMENT_TARGET=99.0 cc -o ././.lake/build/bin/cvx-opt ././.lake/build/ir/Main.c.o.export ././.lake/build/ir/CvxOpt/Basic.c.o.export ././.lake/build/ir/CvxOpt.c.o.export -L /nix/store/72i4gnyvfwlrjdgn22qmyy29331akygf-lean4-4.16.0/lib/lean -lleancpp -lInit -lStd -lLean -lleanrt -lc++ -lLake  /nix/store/r4hyppw0wkgq927siyw36y6x72dg89r7-gmp-with-cxx-6.3.0/lib/libgmp.dylib /nix/store/7vzqfh7dhnzzi9x274fnqfcgjanqm6g7-libuv-1.50.0/lib/libuv.dylib -isysroot/nix/store/lsjl29pwp5if71jfgxlv8fifsrpax805-apple-sdk-11.3/Platforms/MacOSX.platform/Developer/SDKs/MacOSX.sdk

**info:** stderr:

ld: library 'c++' not found

clang: error: linker command failed with exit code 1 (use -v to see invocation)

**error:** external command 'cc' exited with code 1

Some required builds logged failures:

- «cvx-opt»

**error:** build failed
```

fix: add `pkgs.gcc` to nix-shell file -> ✅
# 2025/03/03 syntax highlighting in Sublime Text?
- use VSCode def - https://github.com/leanprover/vscode-lean4/blob/master/vscode-lean4/syntaxes/lean4.json
- convert the `.json` to `.plist` via "PackageDev > Convert (YAML, JSON, PList) to..." - https://forum.sublimetext.com/t/converting-a-json-tmlanguage/66201/4
- rename the `*.plist` file to use the suffix `.tmLanguage`
- move the .tmlang file to your packages folder - https://stackoverflow.com/a/49782144
	- go to Command Palette: "Preferences: Browse Packages" -> reveals a folder
	- make a new folder there for your "package"
	- move the `*.tmLanguage` file to that new folder

# misc references
- all the references - https://leanprover-community.github.io/learn.html
- language reference - https://lean-lang.org/doc/reference/latest/
- mathlib
	- index - https://leanprover-community.github.io/mathlib-overview.html
	- docs - https://leanprover-community.github.io/mathlib4_docs/index.html
- theorem proving in Lean - https://leanprover.github.io/theorem_proving_in_lean4/title_page.html
	- `theorem` vs. `def` - https://leanprover.github.io/theorem_proving_in_lean4/propositions_and_proofs.html#working-with-propositions-as-types
- theorem-proving tactics
	- index - https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_C/Part_C.html
	- cheatsheet - https://leanprover-community.github.io/papers/lean-tactics.pdf
- coding
	- tutorial - https://lean-lang.org/functional_programming_in_lean/