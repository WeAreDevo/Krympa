import re
import sys
import os

LEMMA_VARIANT_RE = re.compile(
    r'^(?:lemma|big_step_lemma|small_step_lemma|abstracted_lemma|conjecture)_(\d+)$'
)

def canon_lemma_variant(name: str) -> str:
    """
    Collapse lemma variants to a single namespace by number:
      big_step_lemma_0001 -> lemma_0001
      small_step_lemma_0001 -> lemma_0001
      abstracted_lemma_0001 -> lemma_0001
      conjecture_0001 -> lemma_0001   (IMPORTANT: conjecture0 is special and NOT touched)
    """
    name = name.strip()
    m = LEMMA_VARIANT_RE.match(name)
    if m:
        return f"lemma_{m.group(1)}"
    return name

VAR_NAMES = ["x","y","z","w","v","u","t","s","r","q","p","o","n","m","l","k","j","i","h","g","f","e","d","c","b","a"]

def vars_in_order(expr: str):
    """Variables in first-appearance order (case-insensitive), excluding op."""
    seen = set()
    out = []
    for m in re.finditer(r"[A-Za-z]\w*", expr):
        v = m.group(0).lower()
        if v == "op":
            continue
        if v not in seen:
            seen.add(v)
            out.append(v)
    return out

def fresh_name(i: int) -> str:
    return VAR_NAMES[i] if i < len(VAR_NAMES) else f"x{i}"

# Recursive parser for op(...) terms into Lean infix ◇
def parse_term(s, i=0):
    n = len(s)
    while i < n and s[i].isspace():
        i += 1
    if i >= n:
        raise ValueError("Unexpected end while parsing term")

    if s.startswith("op(", i):
        i += 3
        left, i = parse_term(s, i)
        while i < n and s[i].isspace():
            i += 1
        if i >= n or s[i] != ',':
            raise ValueError(f"Expected ',' in op(...) at pos {i} in: {s}")
        i += 1
        right, i = parse_term(s, i)
        while i < n and s[i].isspace():
            i += 1
        if i >= n or s[i] != ')':
            raise ValueError(f"Expected ')' in op(...) at pos {i} in: {s}")
        i += 1
        return f"({left} ◇ {right})", i

    m = re.match(r'[A-Za-z]\w*', s[i:])
    if not m:
        raise ValueError(f"Expected variable at pos {i} in: {s}")
    ident = m.group(0)
    return ident, i + len(ident)

def parse_side(side_text):
    side_text = side_text.strip().rstrip('.')
    term, pos = parse_term(side_text, 0)
    while pos < len(side_text) and side_text[pos].isspace():
        pos += 1
    if pos != len(side_text):
        raise ValueError(f"Extra characters after parsed term: '{side_text[pos:]}'")
    return term

def parse_equation_tptp(eq):
    eq = eq.strip()
    if eq.startswith("(") and eq.endswith(")"):
        eq = eq[1:-1].strip()
    depth = 0
    pos_eq = None
    for i, c in enumerate(eq):
        if c == '(':
            depth += 1
        elif c == ')':
            depth -= 1
        elif c == '=' and depth == 0:
            pos_eq = i
            break
    if pos_eq is None:
        lhs = parse_side(eq)
        return lhs, None
    lhs_text = eq[:pos_eq].strip()
    rhs_text = eq[pos_eq + 1:].strip()
    lhs = parse_side(lhs_text)
    rhs = parse_side(rhs_text)
    return lhs, rhs

# Strip TPTP universal quantifiers ! [X,Y,...] :
def strip_forall(expr):
    m = re.match(r"!\s*\[.*?\]\s*:\s*(.*)", expr)
    if m:
        return m.group(1).strip()
    return expr.strip()

# Extract variables
def extract_variables(s):
    vars = sorted(set(re.findall(r"[A-Za-z]\w*", s)))
    if 'op' in vars:
        vars.remove('op')
    return vars

# Parse dependencies from proof lines
def parse_dependencies_from_proof(proof_lines, lemma_num_map=None):
    deps = set()
    lemma_num_map = lemma_num_map or {}

    for line in proof_lines:
        matches = re.findall(r'\((lemma_\d+|small_step_lemma_\d+|big_step_lemma_\d+|abstracted_lemma_\d+|a1|a_1)\)', line)
        for m in matches:
            if m in ("a1", "a_1"):
                deps.add("op_law")
            else:
                deps.add(canon_lemma_variant(m))

        # "by lemma 3" should refer to the lemma 3 of THIS proof block
        matches2 = re.findall(r'by lemma (\d+)', line, flags=re.IGNORECASE)
        for num in matches2:
            deps.add(lemma_num_map.get(num, f"Lemma_{num}"))

    return sorted(deps)

REAL_CONJ = "conjecture0"

def normalize_variables(expr):
    canon_vars = vars_in_order(expr)
    renaming = {v: fresh_name(i) for i, v in enumerate(canon_vars)}

    def repl(match):
        v = match.group(0)
        if v.lower() == "op":
            return v
        return renaming.get(v.lower(), v.lower())

    new_expr = re.sub(r"[A-Za-z]\w*", repl, expr)
    new_vars = [renaming[v] for v in canon_vars]
    return new_expr, new_vars

# Lean abbreviation
def lean_abbrev(name, expr):
    expr_core = strip_forall(expr)
    expr_norm, vars = normalize_variables(expr_core)
    varstr = " ".join(vars)
    lhs, rhs = parse_equation_tptp(expr_norm)
    if rhs is None:
        body = lhs
    else:
        body = f"{lhs} = {rhs}"
    return f"""abbrev Equation_{name} (G : Type _) [Magma G] :=
  ∀ {varstr} : G, {body}
"""

def lean_axiom(name, expr):
    expr_norm, vars = normalize_variables(expr)
    lhs, rhs = parse_equation_tptp(expr_norm)

    if rhs is None:
        body = lhs
    else:
        combined = f"{lhs} = {rhs}"
        if len(combined) > 80:
            # Put the '=' on its own line and rhs indented
            body = f"{lhs} =\n      {rhs}"
        else:
            body = combined

    return f"""axiom {name} (G : Type _) [Magma G] :
  ∀ {' '.join(vars)} : G, {body}
"""

def build_variable_renaming_from_expr(expr):
    canon_vars = vars_in_order(expr)
    return {v: fresh_name(i) for i, v in enumerate(canon_vars)}

def apply_renaming(expr, renaming, allowed_vars=None):
    """
    Rename variables using `renaming`.
    If a variable is NOT in `renaming` (e.g. 'X', 'Y', 'V' introduced by prover),
    then map it to the first variable in `allowed_vars` (binder vars) to avoid
    generating free variables in Lean.
    """
    fallback = None
    if allowed_vars:
        fallback = allowed_vars[0]  # "first var in vars set"

    def repl(match):
        tok = match.group(0)
        low = tok.lower()
        if low == "op":
            return tok

        # normal case: variable was in lemma statement, so it's in renaming
        if low in renaming:
            return renaming[low]

        # prover-introduced variable: force it to a binder var (no free vars)
        if fallback is not None:
            return fallback

        # last resort: lowercase it (keeps behavior if no binders exist)
        return low

    return re.sub(r"[A-Za-z]\w*", repl, expr)

def format_calc_step(lhs, rhs, dep, indent="        ", max_len=80):
    expr_len = len(lhs) + len(rhs)

    if expr_len <= max_len:
        return (
            f"{lhs} = {rhs} := by\n"
            f"{indent}duper [{dep}]"
        )
    else:
        return (
            f"{lhs} =\n"
            f"{indent}{rhs} := by\n"
            f"{indent}duper [{dep}]"
        )
    
def format_lemma_body(lhs, rhs, indent="  ", max_len=80):
    """
    Format the body of a lemma:
      lhs = rhs
    If the total length exceeds max_len, break at the '='.
    """
    if rhs is None:
        # Just lhs
        return lhs
    full = f"{lhs} = {rhs}"
    if len(full) <= max_len:
        return full
    else:
        # break at '='
        return f"{lhs} =\n{indent}{rhs}"

def format_side(expr, indent="      ", max_len=80):
    """
    Format one side of an equation (LHS or RHS) for Lean.
    - Only break lines at the ◇ operator if the line exceeds max_len.
    - Each new line is indented.
    """
    expr = expr.strip()
    if len(expr) <= max_len:
        return expr

    parts = expr.split("◇")
    lines = []
    current = parts[0].strip()

    for part in parts[1:]:
        part = part.strip()
        # Add ◇ to the previous part
        candidate = f"{current} ◇ {part}"
        if len(candidate) > max_len:
            # Break line here
            lines.append(current)
            current = part
        else:
            current = candidate

    lines.append(current)
    # Join with newline + indent
    return ("\n" + indent).join(lines)

def build_calc_block(proof_lines, renaming, lemma_num_map, allowed_vars, name_mapping, axiom_name_map):
    """
    Builds Lean calc block from TPTP proof lines.
    Each step may have:
      lhs
      = { by <dep> }
      rhs

    Converts to:
      lhs = rhs := by duper [dep]
    """
    lines = []

    for i in range(len(proof_lines)):
        line = proof_lines[i].strip()
        if not line or line.lower() == "proof:":
            continue

        
        # Look for a dependency line like "= { by ... }"
        m = re.match(r"=\s*\{\s*by\s+(\S+).*?\}", line)
        if m:
            # Determine dependency (only the first reference)
            refs = re.findall(r"(lemma_\d+|small_step_lemma_\d+|big_step_lemma_\d+|abstracted_lemma_\d+|a1|a_1)", line)
            dep = None
            if refs:
                r = refs[0]
                if r in ("a1","a_1"):
                    dep = "op_law"
                elif r in name_mapping:
                    dep = name_mapping[r]
                else:
                    dep = r
            else:
                # Next, try "lemma N" pattern
                m2 = re.search(r"lemma\s+(\d+)", line, flags=re.IGNORECASE)
                if m2:
                    dep_num = m2.group(1)
                    dep_name = lemma_num_map.get(dep_num, f"Lemma_{dep_num}")
                    dep = name_mapping.get(dep_name, dep_name)

                else:
                    # fallback: just take first word and translate if possible
                    dep = name_mapping.get(line.split()[0], line.split()[0])

            dep_raw = dep
            dep = canon_lemma_variant(dep_raw)

            # prefer proved lemma name if it exists
            dep = name_mapping.get(dep, name_mapping.get(dep_raw, dep))

            # only if not mapped to a lemma, fall back to axiom mapping
            dep = axiom_name_map.get(dep, dep)

            if i == 0 or i + 1 >= len(proof_lines):
                continue
            lhs_raw = apply_renaming(proof_lines[i - 1], renaming, allowed_vars)
            rhs_raw = apply_renaming(proof_lines[i + 1], renaming, allowed_vars)

            lhs, _ = parse_term(lhs_raw)
            rhs, _ = parse_term(rhs_raw)

            lhs_for_step = lhs if not lines else "_"
            lines.append(format_calc_step(lhs_for_step, rhs, dep))
            # lines.append(f"{lhs} = {rhs} := by\n        duper [{dep}]")
            #lines.append(f"_ = {rhs_norm} := by\n        duper [{dep}]")

    return lines

# Lean lemma with dependencies (works for lemmas and conjecture)
def lean_lemma(name, expr, deps_from_proof=[], proof_lines=None, lemma_num_map=None, name_mapping=None, axiom_name_map=None):
    expr_core = strip_forall(expr)

    # variables that are allowed to appear in the Lean statement for this lemma
    renaming = build_variable_renaming_from_expr(expr_core)
    expr_norm = apply_renaming(expr_core, renaming)

    lhs, rhs = parse_equation_tptp(expr_norm)

    vars = [renaming[v] for v in vars_in_order(expr_core)]
    var_list = " ".join(vars)

    body = format_lemma_body(lhs, rhs, indent="      ", max_len=80)

    # LEMMA WITH PROOF LINES: build calc, but collapse single-step calc to "by duper [dep]"
    if name.startswith("lemma_") and proof_lines:
        calc_lines = build_calc_block(
            proof_lines,
            renaming,
            lemma_num_map or {},
            vars,
            name_mapping or {},
            axiom_name_map or {},
        )

        # If calc has exactly one step, don't emit a calc-block at all.
        if len(calc_lines) == 1:
            m = re.search(r"duper\s*\[\s*([^\]]+)\s*\]", calc_lines[0])
            dep = m.group(1).strip() if m else "*"
            return f"""
  have {name} ({var_list} : G) :
  {body} := by
    duper [{dep}]
"""

        calc_block = "\n      ".join(calc_lines)
        return f"""
  have {name} ({var_list} : G) :
  {body} := by
    calc
      {calc_block}
"""

    # CONJECTURE WITH PROOF LINES
    if name == REAL_CONJ and proof_lines:
        calc_lines = build_calc_block(
            proof_lines,
            renaming,
            lemma_num_map or {},
            vars,
            name_mapping or {},
            axiom_name_map or {},
        )

        intros = " ".join(vars)

        if len(calc_lines) == 1:
            m = re.search(r"duper\s*\[\s*([^\]]+)\s*\]", calc_lines[0])
            dep = m.group(1).strip() if m else "*"
            return f"""
  show _ by
    intros {intros}
    duper [{dep}]
"""

        calc_block = "\n      ".join(calc_lines)
        return f"""
  show _ by
    intros {intros}
    calc
      {calc_block}
"""

    # FALLBACK: no proof lines -> regular duper with deps
    deps_str = f"[{', '.join(deps_from_proof)}]" if deps_from_proof else "[*]"
    return f"""
  have {name} ({var_list} : G) :
  {body} := by
    duper {deps_str}
"""

# Main program
if len(sys.argv) != 2:
    print("Usage: python tolean.py input_file")
    sys.exit(1)

input_file = sys.argv[1]
basename = os.path.splitext(os.path.basename(input_file))[0]
project_root = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
output_dir = os.path.join(project_root, "lean", "Proof")
os.makedirs(output_dir, exist_ok=True)
output_file = os.path.join(output_dir, f"{basename}.lean")

axiom = None
conjecture = None
lemmas = {}
inline_axioms = {}        # name -> expr
used_inline_axioms = set()
axiom_name_map = {}       # original -> axiomN
buffer = ""
proof_section = False
current_proof_lines = []
current_lemmaname = None
proofs_by_lemma = {}  # lemma_name -> list of proof lines
proof_block_id = 0
lemma_num_map = {}
proof_block_maps_by_lemma = {}  # lemma_name -> lemma_num_map snapshot

with open(input_file) as f:
    for line in f:
        stripped = line.strip()

        # Inline axioms like: Axiom 2 (a1): op(X, ...)
        m = re.match(r"Axiom\s+\d+\s+\(([^)]+)\):\s*(.*)", stripped)
        if m:
            ax_name_raw = m.group(1).strip()
            ax_expr = m.group(2).rstrip(".")
            ax_name = ax_name_raw if ax_name_raw == "a1" else canon_lemma_variant(ax_name_raw)
            inline_axioms[ax_name] = ax_expr
            continue

        # Start proof section
        if stripped.startswith("The conjecture is true! Here is a proof"):
            proof_section = True
            proof_block_id += 1
            lemma_num_map = {}   # reset numbering per block
            continue

        # Lemmas
        if stripped.startswith("% lemma_") or stripped.startswith("% small_step_lemma_") or stripped.startswith("% big_step_lemma_") or stripped.startswith("% abstracted_lemma_"):
            parts = stripped.split("|")
            body = parts[0]
            deps_part = parts[1] if len(parts) > 1 else ""
            m = re.match(r"%\s*(\S+):\s*(.*)", body)
            if m:
                name_raw, expr = m.group(1), m.group(2)
                # only conjecture0 is special; everything else canonicalize
                name = name_raw if name_raw == REAL_CONJ else canon_lemma_variant(name_raw)
                deps = []
                if "deps:" in deps_part:
                    deps_str = deps_part.split("deps:", 1)[1]

                    # grab only dependency headers like "a_1:" or "lemma_0001:" (ignores X0,X1,X2)
                    # 1) names that appear as "name:"
                    dep_names = re.findall(r'([A-Za-z_]\w*)\s*:', deps_str)

                    # 2) also grab bare lemma/small_step_lemma tokens that might appear without ':'
                    dep_names += re.findall(r'\b(lemma_\d+|small_step_lemma_\d+|big_step_lemma_\d+|abstracted_lemma_\d+)\b', deps_str)

                    # normalize + de-dup (preserve order)
                    seen = set()
                    for d in dep_names:
                        if d in ("a1", "a_1"):
                            d = "op_law"
                        else:
                            d = canon_lemma_variant(d)
                        if d not in seen:
                            deps.append(d)
                            seen.add(d)

                lemmas[name] = (expr, deps)
            continue

        # Parse proof goals if in proof section
        if proof_section:
            m = re.match(r'(?:Goal|Lemma)\s+(\d+)(?:\s*\(([^)]+)\))?\s*:\s*(.*)', stripped)
            if m:
                # If there is a current lemma being accumulated, finalize it
                if current_proof_lines and current_lemmaname and current_lemmaname in lemmas:
                    proofs_by_lemma[current_lemmaname] = current_proof_lines.copy()
                    proof_block_maps_by_lemma[current_lemmaname] = dict(lemma_num_map)
                    deps = parse_dependencies_from_proof(current_proof_lines, lemma_num_map)
                    expr, _ = lemmas[current_lemmaname]
                    lemmas[current_lemmaname] = (expr, deps)
                    current_proof_lines = []

                # Start new lemma
                number = m.group(1)  # this is "3" for "Lemma 3: ..."
                given_name = m.group(2)

                if given_name:
                    # IMPORTANT: only "conjecture0" is the real conjecture
                    if given_name.startswith("conjecture") and given_name != "conjecture0":
                        current_lemmaname = canon_lemma_variant(given_name)   # conjecture_0001 -> lemma_0001
                    else:
                        current_lemmaname = canon_lemma_variant(given_name)   # big_step/small_step/abstracted -> lemma_XXXX
                else:
                    current_lemmaname = f"Lemma_{number}_b{proof_block_id}"

                # record the mapping so "by lemma 3" resolves correctly in this block
                lemma_num_map[number] = current_lemmaname
                lemmaexpr = m.group(3).strip()
                current_proof_lines = []

                # If this goal name was declared as an inline axiom, do NOT treat it as a lemma.
                # Otherwise we "prove" an axiom and later the real axiom never gets emitted.
                if current_lemmaname in inline_axioms:
                    current_lemmaname = None
                    current_proof_lines = []
                    continue

                # Initialize lemma if not 'a1' (hypothesis)
                if ("a1" not in current_lemmaname.lower()) and ("a_1" not in current_lemmaname.lower()):
                    canon_goal = current_lemmaname if current_lemmaname == REAL_CONJ else canon_lemma_variant(current_lemmaname)
                    current_lemmaname = canon_goal
                    lemma_num_map[number] = current_lemmaname

                    lemmas[current_lemmaname] = (lemmaexpr, [])
                continue

            # Accumulate proof lines
            if current_lemmaname:
                if stripped and not stripped.startswith("Goal") and not stripped.startswith("Lemma") and not stripped.startswith("RESULT"):
                    current_proof_lines.append(stripped)
                    # detect usage of inline axioms or lemmas
                    matches = re.findall(r'\((lemma_\d+|small_step_lemma_\d+|big_step_lemma_\d+|abstracted_lemma_\d+|a1|a_1)\)', stripped)
                    for ax in matches:
                        if ax in ("a1", "a_1"):
                            used_inline_axioms.add(ax)
                        else:
                            used_inline_axioms.add(canon_lemma_variant(ax))

            # Finalize current lemma if next Goal/Lemma or RESULT
            if re.match(r'(?:Goal|Lemma)\s+\d+', stripped) or stripped.startswith("RESULT"):
                if current_lemmaname and current_proof_lines:
                    proofs_by_lemma[current_lemmaname] = current_proof_lines.copy()
                    deps = parse_dependencies_from_proof(current_proof_lines, lemma_num_map)
                    proof_block_maps_by_lemma[current_lemmaname] = dict(lemma_num_map)
                    expr, _ = lemmas[current_lemmaname]
                    lemmas[current_lemmaname] = (expr, deps)
                    current_proof_lines = []

        # Accumulate fof(...) blocks
        if "fof(" in stripped:
            buffer = stripped
            if buffer.endswith(")."):
                name = re.search(r"fof\(([^,]+)", buffer).group(1)
                formula_match = re.search(r"fof\([^,]+,[^,]+,(.*)\)\s*\.", buffer, re.DOTALL)
                if formula_match:
                    formula = formula_match.group(1).strip()
                    if "axiom" in buffer:
                        axiom = (name, formula)
                    elif "conjecture" in buffer:
                        conjecture = (name, formula)
                buffer = ""
            continue
        elif buffer:
            buffer += " " + stripped
            if buffer.endswith(")."):
                name = re.search(r"fof\(([^,]+)", buffer).group(1)
                formula_match = re.search(r"fof\([^,]+,[^,]+,(.*)\)\s*\.", buffer, re.DOTALL)
                if formula_match:
                    formula = formula_match.group(1).strip()
                    if "axiom" in buffer:
                        axiom = (name, formula)
                    elif "conjecture" in buffer:
                        conjecture = (name, formula)
                buffer = ""

if axiom is None:
    print("ERROR: Missing axiom or conjecture in TPTP")
    sys.exit(1)

# Normalize axiom names and filter out those already proven
axiom_counter = 1
axiom_name_map = {}  # original inline name -> axiomN
for ax in sorted(used_inline_axioms):
    if ax == "a1":
        continue

    ax_canon = canon_lemma_variant(ax)
    if ax_canon in lemmas:
        # proved as a lemma => do NOT emit as an axiom
        continue

    axiom_name_map[ax_canon] = f"axiom{axiom_counter}"
    axiom_counter += 1

# Normalize lemma names
normalized_lemmas = {}
name_mapping = {}
counter = 1

for old_name in lemmas.keys():
    if old_name == REAL_CONJ:
        new_name = old_name
    else:
        new_name = f"lemma_{counter}"
        counter += 1
    name_mapping[old_name] = new_name
    normalized_lemmas[new_name] = lemmas[old_name]

lemmas = normalized_lemmas
has_conj_lemma = any(old == REAL_CONJ for old in name_mapping.keys())
last_lemma_name = list(lemmas.keys())[-1] if lemmas else None

# Normalize dependencies in lemmas
for lem_name, (expr, deps) in lemmas.items():
    new_deps = [name_mapping.get(d, d) for d in deps]
    lemmas[lem_name] = (expr, new_deps)

# Normalize proof lines dictionary keys
normalized_proofs = {}
for old_name, lines in proofs_by_lemma.items():
    if old_name in name_mapping:
        new_name = name_mapping[old_name]
        normalized_proofs[new_name] = lines
proofs_by_lemma = normalized_proofs

normalized_maps = {}
for old_name, mp in proof_block_maps_by_lemma.items():
    if old_name in name_mapping:
        normalized_maps[name_mapping[old_name]] = mp
proof_block_maps_by_lemma = normalized_maps

# Update lemma dependencies to point to axiom_n if needed
for lemmaname, (expr, deps) in lemmas.items():
    new_deps = []
    for d in deps:
        if d in axiom_name_map:
            new_deps.append(axiom_name_map[d])
        else:
            new_deps.append(d)
    lemmas[lemmaname] = (expr, new_deps)

# Output Lean file
axname, axexpr = axiom
lean_ax = lean_abbrev(axname, axexpr)
conj_vars = []
if conjecture is not None:
    conjname, conjexpr = conjecture
    _, conj_vars = normalize_variables(strip_forall(conjexpr))  # gives ["x","y","z",...]

if conjecture is not None:
    conjname, conjexpr = conjecture
    lean_conj = lean_abbrev(conjname, conjexpr)
else:
    conjname = "no_conjecture"
    lean_conj = ""

# Theorem header
theorem_header = (
    f"theorem Equation_{axname}_implies_Equation_{conjname}"
    f" (G : Type _) [Magma G]\n"
    f"    (op_law : Equation_{axname} G) : "
    f"Equation_{conjname} G :="
)

# Add only axioms that were not proven as lemmas
lean_axioms = ""
for old, new in axiom_name_map.items():
    lean_axioms += lean_axiom(new, inline_axioms[old])

# Add lemmas
lemma_text = ""
for lemmaname, (expr, deps) in lemmas.items():
    proof_lines = proofs_by_lemma.get(lemmaname)
    lmap = proof_block_maps_by_lemma.get(lemmaname, {})
    lemma_text += lean_lemma(lemmaname, expr, deps, proof_lines, lmap, name_mapping, axiom_name_map)

ending = ""

if (not has_conj_lemma) and last_lemma_name:
    # no conjecture at all -> end with last lemma
    if last_lemma_name:
        ending = f"""
  show _ by
    exact {last_lemma_name}
"""
# else:
#     # conjecture exists, but if it was NOT proved as a conjecture-lemma, close goal using last lemma
#     if (not has_conj_lemma) and last_lemma_name:
#         intros = " ".join(conj_vars) if conj_vars else "x y z"
#         args = " ".join(conj_vars) if conj_vars else "x y z"
#         ending = f"""
#   show _ by
#     intro {intros}
#     exact {last_lemma_name} {args}
# """

lean_output = f"""import Mathlib.Tactic.NthRewrite
import Duper
open Lean Grind

set_option linter.style.longLine false

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

{lean_ax}
{lean_axioms}
{lean_conj}
{theorem_header}{lemma_text}{ending}
"""

with open(output_file, "w") as f:
    f.write(lean_output)

print("✓ Generated Lean file:", output_file)
