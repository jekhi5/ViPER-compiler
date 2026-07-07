# ViPER Syntax Highlighting

Extensions for VS Code and TextMate2.

## Structure`

**Always edit `viper.tmLanguage.json` at the root of this directory.** The copies inside `VSCode/` and `TextMate2/` are symlinks and must not be edited directly.

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
