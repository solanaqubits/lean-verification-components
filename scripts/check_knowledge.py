#!/usr/bin/env python3
"""Check the knowledge catalog against Lean sources and local Markdown links.

This checks navigation and coverage, not the meaning of proofs or descriptions.
Run from any directory with Python 3; no third-party dependencies are needed.
"""
import json
import os
import re
from pathlib import Path
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]


def main():
    catalog = json.loads((ROOT / 'knowledge/catalog.json').read_text())
    errors = []
    sections = catalog['sections']
    section_ids = {section['id'] for section in sections}
    if len(section_ids) != len(sections):
        errors.append('Duplicate section IDs')
    for section in sections:
        if not (ROOT / section['index']).is_file():
            errors.append(f"Missing section index: {section['index']}")
    modules = catalog['modules']
    ids = [module['id'] for module in modules]
    if len(ids) != len(set(ids)):
        errors.append('Duplicate module IDs')
    cards = [module['card'] for module in modules]
    if len(cards) != len(set(cards)):
        errors.append('Duplicate card paths')
    sources = {str(path.relative_to(ROOT)) for path in (ROOT / 'Verification').glob('*.lean')}
    indexed = {module['source'] for module in modules}
    if sources != indexed:
        errors.append(f'Coverage mismatch: missing={sources - indexed}, extra={indexed - sources}')
    for module in modules:
        name = module['id']
        if module['section'] not in section_ids:
            errors.append(f'{name}: unknown section')
        if module['source'] != f'Verification/{name}.lean':
            errors.append(f'{name}: inconsistent source path')
        card = (ROOT / module['card']).resolve()
        if not card.is_relative_to((ROOT / 'knowledge').resolve()):
            errors.append(f'{name}: card must remain inside knowledge')
            continue
        if card.name not in (name + '.en.md',):
            errors.append(f'{name}: inconsistent card filename')
        source = ROOT / module['source']
        if not card.is_file() or not source.is_file():
            errors.append(f'{name}: missing card or source')
            continue
        text = card.read_text()
        for field, value in [('id', name), ('language', 'en'),
                             ('section', module['section']), ('source', module['source'])]:
            if f'{field}: {value}\n' not in text:
                errors.append(f'{name}: missing or inconsistent {field} metadata')
        imports = re.findall(r'^import (Verification\.\w+)', source.read_text(), re.M)
        if imports != module['project_imports']:
            errors.append(f'{name}: stale project_imports')
        section = next((s for s in sections if s['id'] == module['section']), None)
        if section:
            section_index = ROOT / section['index']
            relative_card = Path(os.path.relpath(card, section_index.parent)).as_posix()
            if section_index.is_file() and f']({relative_card})' not in section_index.read_text():
                errors.append(f'{name}: absent from section index')
        if module.get('english_card'):
            english = (ROOT / module['english_card']).resolve()
            if not english.is_relative_to((ROOT / 'knowledge').resolve()):
                errors.append(f'{name}: English card must remain inside knowledge')
                continue
            if english.name != name + '.en.md' or not english.is_file():
                errors.append(f'{name}: missing or invalid English card')
                continue
            english_text = english.read_text()
            for field, value in [('id', name), ('language', 'en'),
                                 ('section', module['section']), ('source', module['source'])]:
                if f'{field}: {value}\n' not in english_text:
                    errors.append(f'{name}: inconsistent English {field} metadata')
            if section:
                relative_english = Path(os.path.relpath(english, section_index.parent)).as_posix()
                if section_index.is_file() and f']({relative_english})' not in section_index.read_text():
                    errors.append(f'{name}: English card absent from section index')
    markdown = [*sorted(ROOT.glob('README*.md')), *sorted((ROOT / 'knowledge').rglob('*.md')),
                *sorted((ROOT / 'docs').rglob('*.md'))]
    for path in markdown:
        for target in re.findall(r'\]\(([^\s)]+)\)', path.read_text()):
            url = urlsplit(target)
            if url.scheme or url.netloc or not url.path:
                continue
            destination = (path.parent / unquote(url.path)).resolve()
            if not destination.exists():
                errors.append(f'{path.relative_to(ROOT)}: broken link {target}')
            elif url.fragment.startswith('L') and destination.suffix == '.lean':
                match = re.fullmatch(r'L(\d+)', url.fragment)
                if match and not 1 <= int(match[1]) <= len(destination.read_text().splitlines()):
                    errors.append(f'{path.relative_to(ROOT)}: invalid source line {target}')
    if errors:
        raise SystemExit('\n'.join(errors))
    print(f'Knowledge catalog OK: {len(modules)} modules, {len(sections)} sections; '
          f'local links checked in {len(markdown)} Markdown files.')


if __name__ == '__main__':
    main()
