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
