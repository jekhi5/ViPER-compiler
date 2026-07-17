import json
import pathlib
import plistlib

BASE = pathlib.Path(__file__).parent.parent
SRC = BASE / 'src'

# Grammar
grammar = json.loads((SRC / 'viper.tmLanguage.json').read_text())
grammar.setdefault('uuid', 'F8066248-75AD-4B4C-AA7A-2830B9265321')
syntaxes = BASE / 'TextMate2/ViPER.tmbundle/Syntaxes'
syntaxes.mkdir(parents=True, exist_ok=True)
(syntaxes / 'ViPER.tmLanguage').write_bytes(plistlib.dumps(grammar, fmt=plistlib.FMT_XML))

# Indentation preferences
prefs = {
    'name': 'Indentation Rules',
    'scope': 'source.viper',
    'settings': {
        'disableIndentCorrections': True,
    },
    'uuid': '1F496C0F-5B74-44FB-93CD-6876857E1D23',
}
preferences = BASE / 'TextMate2/ViPER.tmbundle/Preferences'
preferences.mkdir(parents=True, exist_ok=True)
(preferences / 'Indentation.tmPreferences').write_bytes(plistlib.dumps(prefs, fmt=plistlib.FMT_XML))
