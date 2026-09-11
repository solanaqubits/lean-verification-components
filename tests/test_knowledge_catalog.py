import contextlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('check_knowledge', ROOT/'scripts/check_knowledge.py')
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


class KnowledgeCatalogTests(unittest.TestCase):
    def fixture(self, root):
        for directory in ['Verification', 'knowledge/distributed', 'knowledge/09_distributed_systems']:
            (root/directory).mkdir(parents=True, exist_ok=True)
        (root/'README.md').write_text('# Test\n')
        (root/'Verification/Example.lean').write_text('theorem example : True := True.intro\n')
        (root/'knowledge/distributed/README.md').write_text('[Example](../09_distributed_systems/Example.en.md)\n')
        card = 'knowledge/09_distributed_systems/Example.en.md'
        (root/card).write_text('---\nid: Example\nlanguage: en\nsection: distributed\nsource: Verification/Example.lean\n---\n')
        data = {'sections':[{'id':'distributed','index':'knowledge/distributed/README.md'}],
                'modules':[{'id':'Example','section':'distributed','card':card,
                            'source':'Verification/Example.lean','project_imports':[]}]}
        (root/'knowledge/catalog.json').write_text(json.dumps(data))
        return data

    def test_explicit_english_card_path(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); self.fixture(root)
            with patch.object(checker, 'ROOT', root), contextlib.redirect_stdout(io.StringIO()) as output:
                checker.main()
            self.assertIn('1 modules', output.getvalue())

    def test_card_cannot_escape_knowledge_directory(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); data=self.fixture(root)
            data['modules'][0]['card']='README.md'
            (root/'knowledge/catalog.json').write_text(json.dumps(data))
            with patch.object(checker, 'ROOT', root), self.assertRaisesRegex(SystemExit, 'inside knowledge'):
                checker.main()
