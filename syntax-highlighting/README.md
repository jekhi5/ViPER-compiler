# ViPER Syntax Highlighting

Extensions for VS Code and TextMate2.

Edit [viper.tmLanguage.json](viper.tmLanguage.json) to change the grammar and [language-configuration.json](language-configuration.json) to change indentation rules. Both files are the single source of truth and the TextMate2 bundle files are generated from them at release time.

**Do not forget to update the version in [package.json](package.json)!**

## Installing

**VS Code:** install the `.vsix` from the release page via **Extensions -> ··· -> Install from VSIX**.

**TextMate2:** download `ViPER.tmbundle.zip` from the release page, unzip it, and double-click `ViPER.tmbundle`.

A color theme must be active for syntax highlighting to appear. Go to **TextMate → Preferences → Fonts & Colors** and select any non-plain theme (e.g. Twilight, Monokai).

## Updating

**VS Code:** install the new `.vsix` the same way — it replaces the old version automatically.

**TextMate2:** double-clicking a new bundle does **NOT** replace the old one; TextMate2 installs it alongside, causing conflicts. Always remove the old bundle first:

```bash
rm -rf ~/Library/Application\ Support/TextMate/Pristine\ Copy/Bundles/ViPER*.tmbundle
```

Then double-click the new `ViPER.tmbundle`.

## Building

Build from within the `syntax-highlighting` dir.

**VS Code VSIX:**

```bash
npm install -g @vscode/vsce
vsce package --no-dependencies
```

**TextMate2 bundle:**

```bash
python3 generate_textmate_bundle.py
```

The TextMate2 plist files are gitignored and generated from `viper.tmLanguage.json` and `language-configuration.json` at release time.
