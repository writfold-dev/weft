"""Independent raw-language expectations for actual CLI qualification."""

EXAMPLES = {
    'symbolic': ['entailed', 'refuted', 'undetermined'],
    'inconsistent': ['inconsistent-premises'],
    'sets': ['entailed', 'undetermined', 'entailed', 'entailed'],
    'quantifier-models': ['entailed', 'undetermined', 'refuted'],
    'empty-domain': ['entailed', 'refuted'],
}


def review(body: str) -> str:
    return ('review smoke { context "unresolved" at "exact-request"; '
            'profile "weft.symbolic/1"; target plan = proposal "draft"; ' + body + ' }\n')


def scenarios() -> list[tuple[str, bytes, int, list[str]]]:
    cases = [
        ('large-naturals', 'check exact: 18446744073709551616 == 18446744073709551616; '
         'check different: 18446744073709551616 != 18446744073709551617;', 1, ['entailed', 'entailed']),
        ('shadowing', 'check nested: forall x in {7} { exists x in {8} { x == 8 } };', 1, ['entailed']),
        ('dependent-domain', 'check dependent: forall outer in {3,9} { exists inner in {outer} { inner == outer } };', 1, ['entailed']),
        ('set-membership', 'base := {3,9,3}; empty := {}; expanded := {...empty,9,...base}; '
         'check same: expanded == {9,3}; check nonempty: exists x in expanded { true };', 1, ['entailed', 'entailed']),
        ('diamond-origins', 'base := {1}; left := {...base,2}; right := {...base,3}; '
         'diamond := {...left,...right}; need diamond; check same: diamond == {1,2,3};', 1, ['entailed']),
        ('alpha-original', 'check stable: forall x in {1,2} { forall y in {7,8} { x != y and x != 9 } };',
         1, ['entailed']),
        ('alpha-renamed', 'check stable: forall outer in {1,2} { forall inner in {7,8} { outer != inner and outer != 9 } };',
         1, ['entailed']),
        ('failed-set-atomicity', 'good := {1}; bad := {...good,missing}; '
         'check preserved: good == {1}; check unavailable: exists x in bad { true };',
         2, ['entailed', 'not-evaluated']),
        ('nonuniform-witness', 'xs := {0,1}; assume either: p(0) or p(1); '
         'check existence: exists x in xs { p(x) }; check first: p(0); check second: p(1);',
         1, ['entailed', 'undetermined', 'undetermined']),
        ('required-unused', 'asset input = citation "unavailable"; need input; check local: true;', 2, ['entailed']),
        ('invalid-assumption', 'check before: true; assume broken: missing.field == 1; check after: true;',
         2, ['entailed', 'not-evaluated']),
        ('empty-body-validation', 'xs := {}; check bad: forall x in xs { missing.field == 1 };', 2, ['not-evaluated']),
        ('mixed-set', 'xs := {1,"1"}; check bad: exists x in xs { true };', 2, ['not-evaluated']),
        ('no-let-alias', 'let xs := {1};', 2, []),
        ('typed-no-coercion', 'check bad: 1 == "1";', 2, ['not-evaluated']),
    ]
    result = [(name, review(body).encode(), code, verdicts) for name, body, code, verdicts in cases]
    atoms = ' and '.join(f'(p{n}() or not p{n}())' for n in range(17))
    result.append(('valuation-limit', review(f'check bounded: {atoms};').encode(), 2, ['unknown']))
    premises = ' '.join(f'assume h{n}: true;' for n in range(1000))
    atoms = ' and '.join(f'(p{n}() or not p{n}())' for n in range(12))
    result.append(('output-limit', review(f'{premises} check bounded: {atoms};').encode(), 2, []))
    result.append(('invalid-utf8', bytes([0xff, 0x1b, 0, 0xc0]), 2, []))
    return result
