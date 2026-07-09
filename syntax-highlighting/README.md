# ViPER Syntax Highlighting

Extensions for VS Code and TextMate2.

## Structure`

**Always edit `viper.tmLanguage.json` at the root of this directory.** The copies inside `VSCode/` and `TextMate2/` are symlinks and must not be edited directly.

**Do not forget to update the version in the [VSCode/package.json](VSCode/package.json) file. If you do not, your release upload will fail as there is already an existing release with that tag number!**

## Building

**VS Code VSIX:**

```bash
npm install -g @vscode/vsce
(cd VSCode && vsce package --no-dependencies)
```

**TextMate2 bundle** (resolves symlinks for distribution):

```bash
cp -rL TextMate2/ViPER.tmbundle /tmp/ViPER.tmbundle
cd /tmp && zip -r ViPER.tmbundle.zip ViPER.tmbundle
```
