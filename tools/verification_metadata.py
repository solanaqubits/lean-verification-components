"""Declarative registry data. No commands, proof bodies or admission rules here."""
import argparse
import json
from pathlib import Path
import re

BATCHES = 'tools/verification_batches.json'
RECIPES = 'tools/integration_targets.json'
CATALOG = 'knowledge/catalog.json'
DATA_FILES = {BATCHES, RECIPES, CATALOG}
IDENT = r'[A-Za-z_][A-Za-z_0-9₀₁₂₃₄₅₆₇₈₉]*'
QUALIFIED = IDENT + r'(?:\.' + IDENT + r')*'
REFERENCE = QUALIFIED + r'(?:\.\{' + IDENT + r'(?:,\s*' + IDENT + r')*\})?'


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('Duplicate JSON key: ' + key)
        result[key] = value
    return result


def read_json(text):
    return json.loads(text, object_pairs_hook=unique_object)


def validate_recipe(module, row, modules):
    required = {'suite_struct', 'suite_type', 'parent', 'field', 'constructor', 'proof'}
    optional = {'parent_module', 'universes', 'registry_type'}
    if module not in modules or not isinstance(row, dict) or not required <= row.keys() or row.keys() - required - optional:
        raise ValueError('Invalid recipe: ' + module)
    for key in required | ({'registry_type'} & row.keys()):
        pattern = REFERENCE if key in {'suite_type', 'proof', 'registry_type'} else IDENT
        if key == 'proof':
            pattern = r'(?:by\s+exact\s+)?' + pattern
        if not isinstance(row[key], str) or not re.fullmatch(pattern, row[key]):
            raise ValueError('Recipe must contain names, not executable Lean: ' + module + '/' + key)
    if row.get('parent_module', 'Verification.MasterSuite') not in {
            'Verification.MasterSuite', 'Verification.MasterSuiteComponents'}:
        raise ValueError('Invalid integration parent')
    us = row.get('universes', [])
    if not isinstance(us, list) or any(not isinstance(u, str) or not re.fullmatch(IDENT, u) for u in us) or len(us) != len(set(us)):
        raise ValueError('Invalid universes')


def load_metadata(root, modules, reader=None):
    root = Path(root)
    def read(name, default):
        text = reader(name) if reader else ((root / name).read_text() if (root / name).exists() else None)
        return read_json(text) if text is not None else default
    catalog = read(CATALOG, {'sections': [], 'modules': []})
    sections = [s['id'] for s in catalog['sections']]
    owners = {}
    if len(set(sections)) != len(sections):
        raise ValueError('Duplicate catalog section')
    for row in catalog['modules']:
        name = 'Verification.' + row['id']
        if name in owners or name not in modules or row['section'] not in sections:
            raise ValueError('Invalid catalog module: ' + name)
        owners[name] = row['section']
    data = read(BATCHES, {'schema_version': 1, 'batches': {}})
    if data.get('schema_version') != 1 or data.keys() - {'schema_version', 'policy', 'batches', 'infrastructure_batches'}:
        raise ValueError('Invalid batch schema')
    batches = data['batches']
    if not isinstance(batches, dict):
        raise ValueError('Invalid batches')
    for name, row in batches.items():
        if not isinstance(row, dict) or set(row) - {'direction', 'modules', 'description'} or not {'direction', 'modules'} <= row.keys():
            raise ValueError('Unknown batch fields: ' + name)
        direction, members = row['direction'], row['modules']
        if not isinstance(direction, str) or not name.startswith(direction + '/') or direction not in sections:
            raise ValueError('Invalid batch direction: ' + name)
        if not isinstance(members, list) or not members or any(not isinstance(n, str) for n in members) or len(set(members)) != len(members):
            raise ValueError('Invalid batch members: ' + name)
        if any(n not in modules or owners.get(n) != direction for n in members):
            raise ValueError('Unknown or cross-direction batch member: ' + name)
        if 'description' in row and not isinstance(row['description'], str):
            raise ValueError('Invalid batch description')
    infrastructure = data.get('infrastructure_batches', {})
    if not isinstance(infrastructure, dict):
        raise ValueError('Invalid infrastructure batches')
    for name, row in infrastructure.items():
        if not re.fullmatch(r'[a-z0-9-]+', name) or not isinstance(row, dict) or set(row) != {'description'} or not isinstance(row['description'], str):
            raise ValueError('Infrastructure batches may only describe work, not change checking rules')
    recipes = read(RECIPES, {})
    for name, row in recipes.items():
        validate_recipe(name, row, modules)
    return dict(catalog=catalog, owners=owners, sections=sections, batches=batches, infrastructure_batches=infrastructure, recipes=recipes)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--project', type=Path, default=Path(__file__).resolve().parents[1])
    args = p.parse_args()
    from verification_plan import graph
    try:
        data = load_metadata(args.project, graph(args.project))
        print(json.dumps(dict(ok=True, batches=len(data['batches']), recipes=len(data['recipes']))))
    except (ValueError, OSError, KeyError, TypeError) as e:
        p.exit(1, str(e) + '\n')


if __name__ == '__main__':
    main()
