from itertools import combinations as itertools_combinations
from itertools import product
from typing import Callable, Dict, Iterator, Tuple, Optional, Set
import re
from sympy import sqrt, Rational, sympify, expand, Mul, Add, Symbol
from tqdm import tqdm
import time
from functools import lru_cache
import math
import sys


mode = 0   # Mode: 0 - basic mode, 1 - single combination check mode

user_combination = "mx lx Py + mx ly Px + my lx Px + -my ly Py"   # User combination for single check mode

max_terms = 4   # maximum number of terms in linear combination

"""Vectors (E; P; H; m; l; j; q)"""
vectors_input = "m l P".split()

"""Cipher library"""
ems_code = "!1 (-,-) 3z (+,+) 2x (-,-)".split() # Cr2O3
# ems_code = "!1 (-) 4z (-) 2xy (+)".split() # DyPO4
# ems_code = "!1 (-) 4z (+) 2xy (-)".split() # Mn2Au

# m l l l
# ems_code = "!1 (+) 4z (-) 3z (+)".split() # 6 terms 1 inv

# m l P
# ems_code = "!1 (-)".split() # 1 terms 27 inv
# ems_code = "!1 (-) 2z (+)".split() # 1 terms 13 inv
# ems_code = "!1 (-) 2z (-)".split() # 1 terms 14 inv
# ems_code = "!1 (-) 2x (+) 2y (+,+)".split() # 1 terms 6 inv
# ems_code = "!1 (-) 2x (+) 2y (-)".split() # 1 terms 7 inv
# ems_code = "!1 (-) 2x (-) 2y (+)".split() # 1 terms 7 inv
# ems_code = "!1 (-) 2x (-) 2y (-)".split() # 1 terms 7 inv
# ems_code = "!1 (-) 4z (+)".split() # 2 terms 7 inv
# ems_code = "!1 (-) 4z (-)".split() # 2 terms 6 inv
# ems_code = "!1 (-) 4z (+) 2xy (+)".split() # 2 terms 3 inv
# ems_code = "!1 (-) 4z (-) 2xy (+)".split() # 2 terms 3 inv
# ems_code = "!1 (-) 4z (+) 2xy (-)".split() # 2 terms 4 inv
# ems_code = "!1 (-) 4z (-) 2xy (-)".split() # 2 terms 3 inv
# ems_code = "!1 (-) 3z (+)".split() # 4 terms 9 inv
# ems_code = "!1 (-) 2x (+) 3z (+)".split() # 4 terms 4 inv
# ems_code = "!1 (-) 2x (-) 3z (+)".split() # 4 terms 5 inv
# ems_code = "!1 (-) 6z (+)".split() # 2 terms 7 inv
# ems_code = "!1 (-) 6z (-)".split() # 4 terms 2 inv
# ems_code = "!1 (-) 2x (+) 6z (+)".split() # 2 terms 3 inv
# ems_code = "!1 (-) 2x (-) 6z (+)".split() # 2 terms 4 inv
# ems_code = "!1 (-) 2x (+) 6z (-)".split() # 4 terms 1 inv
# ems_code = "!1 (-) 2x (-) 6z (-)".split() # 4 terms 1 inv
# ems_code = "!1 (-) 2z (+) 3xyz (+)".split() # 3 terms 2 inv
# ems_code = "!1 (-) 4z (+) 3xyz (+)".split() # 6 terms 1 inv
# ems_code = "!1 (-) 4z (-) 3xyz (+)".split() # 6 terms 1 inv

# Operations: 1 !1 2z 2x 2y 2xy mz mx my mxy 3z 3xyz 4z 6z


"""Vector sets"""
POLAR = ['E', 'P', 'j']
AXIAL = ['H', 'm']
NEEL = ['l']
AFE = ['q']

SYMBOL_CACHE = {}
for name in vectors_input:
    for coord in ['x', 'y', 'z']:
        SYMBOL_CACHE[f"{name}{coord}"] = Symbol(f"{name}{coord}")
        SYMBOL_CACHE[f"-{name}{coord}"] = -Symbol(f"{name}{coord}")


def time_invariant(vectors_input):
    t_odd_vectors = {'m', 'l', 'j', 'H'}
    t_even_vectors = {'E', 'q', 'P'}

    minus_count = 0
    for elem in vectors_input:
        if elem in t_odd_vectors:
            minus_count += 1
        elif elem not in t_even_vectors:
            print(f"Unknown vector type: {elem}")
            return None

    print("time invariant" if minus_count % 2 == 0 else "not time invariant")

def format_ems_code(ems_code):
    formatted = []
    i = 0
    n = len(ems_code)
    while i < n:
        current = ems_code[i]
        next_item = ems_code[i + 1] if i + 1 < n else None
        if next_item and next_item.startswith('('):
            formatted.append(current + next_item)
            i += 2
        else:
            formatted.append(current)
            i += 1
    return ' '.join(formatted)

def expand_vectors(vector_names):
    return [[f"{name}x", f"{name}y", f"{name}z"] for name in vector_names]


"""Combination generator"""

def generate_combinations_iter(vectors: list, max_term: int) -> Iterator[Tuple[str, ...]]:
    vector_products = [' '.join(prod) for prod in product(*vectors)]

    yield from ((term,) for term in vector_products)

    for term_count in range(2, max_term + 1):
        for terms in itertools_combinations(vector_products, term_count):
            yield terms
            for minus_count in range(1, len(terms)):
                for minus_positions in itertools_combinations(range(len(terms)), minus_count):
                    new_terms = list(terms)
                    for pos in minus_positions:
                        new_terms[pos] = f"-{new_terms[pos]}"
                    yield tuple(new_terms)

def combination_to_str(comb: Tuple[str, ...]) -> str:
    return " + ".join(comb)


"""Cipher parsing"""

@lru_cache(maxsize=None)
def parse_ems_cached(input_tuple):
    ems_code = list(input_tuple)
    user_operation = []
    neel_sign = []
    afe_sign = []

    i = 0
    while i < len(ems_code):
        if not re.search(r'[()]', ems_code[i]):
            user_operation.append(ems_code[i])
            i += 1
        else:
            signs_block = []
            while i < len(ems_code) and re.search(r'[()+-]', ems_code[i]):
                signs_block.append(ems_code[i])
                i += 1

            signs = re.findall(r'[+-]', ' '.join(signs_block))
            neel_sign.append(signs[0] if signs else '+')
            afe_sign.append(signs[1] if len(signs) > 1 else None)

    if '!1' in user_operation:
        inversion_index = user_operation.index('!1')
        current_neel_sign = neel_sign[inversion_index]
        current_afe_sign = afe_sign[inversion_index]

        minus_count = 0
        for vector in vectors_input:
            clean_vector = vector.lstrip('-')
            if clean_vector in POLAR:
                minus_count += 1
            elif clean_vector in NEEL:
                if current_neel_sign == '-':
                    minus_count += 1
            elif clean_vector in AFE:
                if current_afe_sign != '-':
                    minus_count += 1

        if minus_count % 2 != 0:
            print('not space invariant')
            sys.exit(0)

        del user_operation[inversion_index]
        del neel_sign[inversion_index]
        if current_afe_sign is not None:
            del afe_sign[inversion_index]

    return user_operation, neel_sign, afe_sign

def parse_ems(ems_code):
    return parse_ems_cached(tuple(ems_code))

@lru_cache(maxsize=1024)
def cached_sympify(component: str):
    if component in SYMBOL_CACHE:
        return SYMBOL_CACHE[component]
    return sympify(component)

def format_term(term):
    coeff, vars = term.as_coeff_mul()
    vars_str = ' '.join(str(v) for v in vars)

    if coeff == 1:
        return vars_str
    if coeff == -1:
        return f"- {vars_str}"

    sqrt3_part = ""
    other_part = coeff
    if isinstance(coeff, Mul):
        parts = []
        for arg in coeff.args:
            if isinstance(arg, sqrt) and arg.args[0] == 3:
                sqrt3_part = "sqrt(3)"
            else:
                parts.append(arg)
        if parts:
            other_part = Mul(*parts)

    coeff_str = ""
    if sqrt3_part:
        if other_part == 1:
            coeff_str = sqrt3_part
        elif other_part == -1:
            coeff_str = f"-{sqrt3_part}"
        else:
            coeff_str = f"{other_part}*{sqrt3_part}"
    else:
        coeff_str = str(other_part)

    return f"+ {coeff_str} {vars_str}" if coeff > 0 else f"- {coeff_str[1:] if coeff_str.startswith('-') else coeff_str} {vars_str}"

def apply_operation(component: str, operation: str, neel_sign: str, afe_sign: str | None) -> str:
    if operation not in OPERATIONS:
        print(f"Unknown operation: {operation}")
        sys.exit(0)
    return OPERATIONS[operation](component, neel_sign, afe_sign)

def process_combination(combination: str, operation: str, neel_sign: str, afe_sign: str | None) -> str:
    terms = [term.strip() for term in combination.split('+')]
    processed_terms = []
    for term in terms:
        components = term.split()
        processed = [apply_operation(comp, operation, neel_sign, afe_sign) for comp in components]
        processed_terms.append(" ".join(processed))
    return " + ".join(processed_terms)

def process_combination2(combination: str, operation: str, neel_sign: str, afe_sign: Optional[str]) -> str:
    terms = [term.strip() for term in combination.split('+')]
    processed_terms = []
    for term in terms:
        components = term.split()
        processed = [apply_operation(comp, operation, neel_sign, afe_sign) for comp in components]
        product = Mul(*[cached_sympify(p) for p in processed])
        processed_terms.append(expand(product))
    total_expr = Add(*processed_terms)
    terms = total_expr.args if isinstance(total_expr, Add) else [total_expr]
    result = []
    for term in terms:
        formatted = format_term(term)
        if formatted.startswith('+'):
            result.append(f"+ {formatted[2:]}")
        elif formatted.startswith('-'):
            result.append(f"+ -{formatted[2:]}")
        else:
            result.append(f"+ {formatted}")
    final_result = ' '.join(result)
    return final_result[2:] if final_result.startswith('+ ') else final_result


"""Basic operations"""

def apply_base_operation(component: str, operation: str, neel_sign: str, afe_sign: str | None) -> str:
    vector_name = component.lstrip('-')[:-1]
    index = component[-1]
    is_negated = component.startswith('-')
    if operation == "2z":
        if index in ['x', 'y']:
            base_sign = '-'
        else:
            base_sign = ''
    elif operation == "2x":
        base_sign = '' if index == 'x' else '-'
    elif operation == "2y":
        base_sign = '' if index == 'y' else '-'
    elif operation == "2xy":
        if index == 'x':
            new_index = 'y'
            base_sign = ''
        elif index == 'y':
            new_index = 'x'
            base_sign = ''
        else:
            new_index = 'z'
            base_sign = '-'
        index = new_index
    elif operation == "mz":
        if (vector_name in POLAR and index == 'z') or (vector_name in AXIAL and index in ['x', 'y']) or (vector_name in AFE and index == 'z'):
            base_sign = '-'
        else:
            base_sign = ''
    elif operation == "mx":
        if (vector_name in POLAR and index == 'x') or (vector_name in AXIAL and index in ['z', 'y']) or (vector_name in AFE and index == 'x'):
            base_sign = '-'
        else:
            base_sign = ''
    elif operation == "my":
        if (vector_name in POLAR and index == 'y') or (vector_name in AXIAL and index in ['z', 'x']) or (vector_name in AFE and index == 'y'):
            base_sign = '-'
        else:
            base_sign = ''
    elif operation == "mxy":
        if index == 'x':
            new_index = 'y'
            base_sign = '-'
        elif index == 'y':
            new_index = 'x'
            base_sign = '-'
        else:
            new_index = 'z'
            base_sign = ''
        index = new_index
    elif operation == "3xyz":
        if index == 'x':
            new_index = 'y'
        elif index == 'y':
            new_index = 'z'
        else:
            new_index = 'x'
        index = new_index
        base_sign = ''
    elif operation == "4z":
        if index == 'x':
            new_index = 'y'
            base_sign = ''
        elif index == 'y':
            new_index = 'x'
            base_sign = '-'
        else:
            new_index = 'z'
            base_sign = ''
        index = new_index
    else:
        print(f"Unknown operation: {operation}")
        sys.exit(0)
    if vector_name in NEEL:
        if (base_sign == '-' and neel_sign == '+') or (base_sign == '' and neel_sign == '-'):
            final_sign = '-'
        else:
            final_sign = ''
    elif vector_name in AFE and afe_sign is not None:
        if (base_sign == '-' and afe_sign == '+') or (base_sign == '' and afe_sign == '-'):
            final_sign = '-'
        else:
            final_sign = ''
    else:
        final_sign = base_sign
    if is_negated:
        final_sign = '-' if not final_sign else ''
    return f"{final_sign}{vector_name}{index}" if final_sign else f"{vector_name}{index}"


"""Complex operations (3z and 6z)"""

def apply_rotation_3z(component: str, neel_sign: str, afe_sign: Optional[str]):
    sign = -1 if component.startswith('-') else 1
    clean_component = component.lstrip('-')
    vector_name = clean_component[0]
    index = clean_component[1]
    if index == 'x':
        x_part = Rational(-1,2)
        y_part = -sqrt(3)/2
    elif index == 'y':
        x_part = sqrt(3)/2
        y_part = Rational(-1,2)
    else:
        if vector_name in NEEL:
            return -sign * cached_sympify(clean_component) if neel_sign == '-' else sign * cached_sympify(clean_component)
        elif vector_name in AFE:
            return -sign * cached_sympify(clean_component) if afe_sign == '-' else sign * cached_sympify(clean_component)
        else:
            return sign * cached_sympify(clean_component)
    if vector_name in NEEL:
        base = x_part * cached_sympify(f"{vector_name}x") + y_part * cached_sympify(f"{vector_name}y")
        return sign * (-base if neel_sign == '-' else base)
    elif vector_name in AFE:
        base = x_part * cached_sympify(f"{vector_name}x") + y_part * cached_sympify(f"{vector_name}y")
        return sign * (-base if afe_sign == '-' else base)
    else:
        return sign * (x_part * cached_sympify(f"{vector_name}x") + y_part * cached_sympify(f"{vector_name}y"))

def apply_rotation_6z(component: str, neel_sign: str, afe_sign: Optional[str]):
    sign = -1 if component.startswith('-') else 1
    clean_component = component.lstrip('-')
    vector_name = clean_component[0]
    index = clean_component[1]
    if index == 'x':
        x_part = Rational(1,2)
        y_part = sqrt(3)/2
    elif index == 'y':
        x_part = -sqrt(3)/2
        y_part = Rational(1,2)
    else:
        if vector_name in NEEL:
            return -sign * cached_sympify(clean_component) if neel_sign == '-' else sign * cached_sympify(clean_component)
        elif vector_name in AFE:
            return -sign * cached_sympify(clean_component) if afe_sign == '-' else sign * cached_sympify(clean_component)
        else:
            return sign * cached_sympify(clean_component)
    if vector_name in NEEL:
        base = x_part * cached_sympify(f"{vector_name}x") + y_part * cached_sympify(f"{vector_name}y")
        return sign * (-base if neel_sign == '-' else base)
    elif vector_name in AFE:
        base = x_part * cached_sympify(f"{vector_name}x") + y_part * cached_sympify(f"{vector_name}y")
        return sign * (-base if afe_sign == '-' else base)
    else:
        return sign * (x_part * cached_sympify(f"{vector_name}x") + y_part * cached_sympify(f"{vector_name}y"))


OPERATIONS = {
    "2z": lambda c, n, a: apply_base_operation(c, "2z", n, a),
    "2x": lambda c, n, a: apply_base_operation(c, "2x", n, a),
    "2y": lambda c, n, a: apply_base_operation(c, "2y", n, a),
    "2xy": lambda c, n, a: apply_base_operation(c, "2xy", n, a),
    "mz": lambda c, n, a: apply_base_operation(c, "mz", n, a),
    "mx": lambda c, n, a: apply_base_operation(c, "mx", n, a),
    "my": lambda c, n, a: apply_base_operation(c, "my", n, a),
    "mxy": lambda c, n, a: apply_base_operation(c, "mxy", n, a),
    "3z": apply_rotation_3z,
    "3xyz": lambda c, n, a: apply_base_operation(c, "3xyz", n, a),
    "4z": lambda c, n, a: apply_base_operation(c, "4z", n, a),
    "6z": apply_rotation_6z
}


"""Invariance checking"""

@lru_cache(maxsize=1024)
def normalize_combination_cached(comb: str) -> tuple:
    terms = [term.strip() for term in comb.split('+') if term.strip()]
    normalized_terms = []
    for term in terms:
        components = term.split()
        total_minuses = 0
        clean_components = []
        for comp in components:
            minus_count = 0
            while comp.startswith('-'):
                minus_count += 1
                comp = comp[1:]
            total_minuses += minus_count
            clean_components.append(comp)
        split_comps = [(c[:-1], c[-1]) if c[-1] in ('x', 'y', 'z') else (c, '') for c in clean_components]
        split_comps.sort(key=lambda x: (x[0], {'x': 0, 'y': 1, 'z': 2, '': 3}[x[1]]))
        sorted_components = [f"{typ}{idx}" if idx else typ for typ, idx in split_comps]
        if total_minuses % 2 != 0 and sorted_components:
            sorted_components[0] = f"-{sorted_components[0]}"
        normalized_terms.append(' '.join(sorted_components))
    return tuple(sorted(normalized_terms))


def is_invariant(original: str, transformed: str) -> bool:
    return normalize_combination_cached(original) == normalize_combination_cached(transformed)


"""UNIQUENESS FILTER - check if combination contains already found invariants"""

def contains_invariant(combination: str, invariants: Set[Tuple[str, ...]]) -> bool:

    current_terms = set(normalize_combination_cached(combination))

    for invariant_tuple in invariants:
        invariant_set = set(invariant_tuple)

        if invariant_set.issubset(current_terms):
            return True

        negated_invariant = set()
        for term in invariant_tuple:
            if term.startswith('-'):
                negated_invariant.add(term[1:])
            else:
                negated_invariant.add(f"-{term}")

        if negated_invariant.issubset(current_terms):
            return True

    return False


"""Invariant search"""

def check_combination_invariance(combination: str, operations: list, neel_signs: list, afe_signs: list) -> bool:
    # Sort operations: simple operations first, then complex ones
    simple_ops = [op for op in operations if op not in ['3z', '6z']]
    complex_ops = [op for op in operations if op in ['3z', '6z']]

    sorted_ops = simple_ops + complex_ops
    sorted_neel = []
    sorted_afe = []

    for op in sorted_ops:
        idx = operations.index(op)
        sorted_neel.append(neel_signs[idx])
        sorted_afe.append(afe_signs[idx])

    for i, op in enumerate(sorted_ops):
        if op in ['3z', '6z']:
            transformed = process_combination2(combination, op, sorted_neel[i], sorted_afe[i])
        else:
            transformed = process_combination(combination, op, sorted_neel[i], sorted_afe[i])

        if not is_invariant(combination, transformed):
            return False
    return True

def estimate_total_combinations(vectors: list, max_term: int) -> int:
    vector_products = [' '.join(prod) for prod in product(*vectors)]
    n = len(vector_products)
    total = n
    for k in range(2, max_term + 1):
        total += math.comb(n, k)
        for m in range(1, k):
            total += math.comb(n, k) * math.comb(k, m)
    return total

def format_invariant(invariant: str) -> str:
    terms = []
    current_term = []
    current_sign = '+'
    tokens = re.findall(r'([+-]|\w+)', invariant)
    for token in tokens:
        if token in '+-':
            if current_term:
                terms.append((current_sign, ' '.join(current_term)))
                current_term = []
            current_sign = token
        else:
            current_term.append(token)
    if current_term:
        terms.append((current_sign, ' '.join(current_term)))
    if len(terms) <= 1:
        sign, term = terms[0] if terms else ('', '')
        return f"{sign}{term}" if sign == '-' else term
    def find_common_factor(term_group):
        if not term_group:
            return None
        first_factors = set(term_group[0][1].split())
        for factor in first_factors:
            is_common = True
            for sign, term in term_group[1:]:
                term_factors = set(term.split())
                if factor not in term_factors:
                    is_common = False
                    break
            if is_common:
                return factor
        return None
    grouped_terms = []
    remaining_terms = terms.copy()
    while remaining_terms:
        best_group = []
        best_factor = None
        for i in range(len(remaining_terms)):
            current_group = [remaining_terms[i]]
            current_factor = find_common_factor(current_group)
            for j in range(i+1, len(remaining_terms)):
                test_group = current_group + [remaining_terms[j]]
                test_factor = find_common_factor(test_group)
                if test_factor is not None:
                    current_group = test_group
                    current_factor = test_factor
            if len(current_group) > len(best_group):
                best_group = current_group
                best_factor = current_factor
        if best_factor and len(best_group) >= 1:
            inner_terms = []
            for sign, term in best_group:
                remaining_factors = term.split()
                remaining_factors.remove(best_factor)
                remaining_str = ' '.join(remaining_factors)
                if sign == '-':
                    inner_term = f"- {remaining_str}" if remaining_str else "-"
                else:
                    inner_term = remaining_str if remaining_str else "+"
                inner_terms.append(inner_term)
            inner_expr = ' + '.join(inner_terms).replace('+ -', '- ')
            if inner_expr.startswith('-'):
                parts = inner_expr.split(' + ')
                if len(parts) > 1:
                    first = parts[0].lstrip('-').strip()
                    second = parts[1]
                    inner_expr = f"{second} - {first}"
                    if len(parts) > 2:
                        inner_expr += ' + ' + ' + '.join(parts[2:])
            grouped_terms.append((best_factor, inner_expr))
            for term in best_group:
                if term in remaining_terms:
                    remaining_terms.remove(term)
        else:
            sign, term = remaining_terms.pop(0)
            grouped_terms.append((None, f"{sign}{term}" if sign == '-' else term))
    result_parts = []
    for factor, expr in grouped_terms:
        if factor is not None:
            result_parts.append(f"{factor} ({expr})")
        else:
            result_parts.append(expr)
    result = ' + '.join(result_parts).replace('+ -', '- ')
    if result.startswith('+ '):
        result = result[2:]
    result = re.sub(r'\(\s+', '(', result)
    result = re.sub(r'\s+\)', ')', result)
    return result

def find_invariants(vectors: list, max_term: int, operations: list, neel_signs: list, afe_signs: list) -> list:
    invariants = []
    total_combinations = estimate_total_combinations(vectors, max_term)

    found_invariants_set = set()

    with tqdm(total=total_combinations, desc="Searching invariants", bar_format="{l_bar}{bar}| {n_fmt}/{total_fmt} [{elapsed}<{remaining}, {rate_fmt}]") as pbar:
        for comb_tuple in generate_combinations_iter(vectors, max_term):
            comb_str = combination_to_str(comb_tuple)

            if found_invariants_set and contains_invariant(comb_str, found_invariants_set):
                pbar.update(1)
                continue

            try:
                if check_combination_invariance(comb_str, operations, neel_signs, afe_signs):
                    formatted_inv = format_invariant(comb_str)
                    invariants.append(comb_str)
                    found_invariants_set.add(normalize_combination_cached(comb_str))
                    print(f"\r{formatted_inv}")
            except SystemExit:
                return []
            pbar.update(1)

    return invariants


"""Single combination check function"""

def check_single_combination_invariance(combination: str, operations: list, neel_signs: list, afe_signs: list) -> bool:
    # Added calls to parse_ems_cached and time_invariant
    parse_ems_cached(tuple(ems_code))
    time_invariant(vectors_input)

    try:
        return check_combination_invariance(combination, operations, neel_signs, afe_signs)
    except SystemExit:
        return False


if __name__ == "__main__":
    vectors = expand_vectors(vectors_input)

    try:
        user_operation, neel_sign, afe_sign = parse_ems(ems_code)
    except TypeError:
        sys.exit(0)

    if mode == 1:
        print(f"Exchange magnetic structure: {format_ems_code(ems_code)}")
        print(f"\nChecking combination: {user_combination}")

        is_invariant = check_single_combination_invariance(user_combination, user_operation, neel_sign, afe_sign)

        if '!1' in ems_code:
            print("space invariant")

        if is_invariant:
            print("\ninvariant ✅")
        else:
            print("\nnot invariant ❌")

        sys.exit(0)

    if user_operation is not None:
        start_time = time.time()

        print("Vectors:")
        print(' '.join(vectors_input))
        time_invariant(vectors_input)
        if '!1' in ems_code:
            print("space invariant")

        print("\nExchange magnetic structure:")
        print(format_ems_code(ems_code))

        print("\nMaximum number of terms:", max_terms)
        print()

        try:
            invariants = find_invariants(vectors, max_terms, user_operation, neel_sign, afe_sign)
        except SystemExit:
            sys.exit(0)

        elapsed_time = time.time() - start_time

        print(f"\nFound invariant combinations: {len(invariants)}")
        print(f"\nTime taken: {elapsed_time:.2f} seconds")
