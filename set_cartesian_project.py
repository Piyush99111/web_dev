"""
=============================================================
  DISCRETE MATHEMATICS PROJECT
  Topic : Set Operations + Cartesian Product Applications
  Concepts: Sets, Relations, Warshall's Algorithm
=============================================================
"""

from itertools import combinations
import os

# ─────────────────────────────────────────
#  ANSI colour helpers (work on most terminals)
# ─────────────────────────────────────────
BOLD  = "\033[1m"
CYAN  = "\033[96m"
GREEN = "\033[92m"
YELLOW= "\033[93m"
RED   = "\033[91m"
BLUE  = "\033[94m"
MAGENTA = "\033[95m"
RESET = "\033[0m"

def header(text):
    w = 60
    print(f"\n{CYAN}{'═'*w}{RESET}")
    print(f"{CYAN}  {BOLD}{text}{RESET}")
    print(f"{CYAN}{'═'*w}{RESET}")

def section(text):
    print(f"\n{YELLOW}{'─'*50}{RESET}")
    print(f"{YELLOW}  {text}{RESET}")
    print(f"{YELLOW}{'─'*50}{RESET}")

def ok(text):   print(f"  {GREEN}✔  {text}{RESET}")
def info(text): print(f"  {BLUE}ℹ  {text}{RESET}")
def warn(text): print(f"  {RED}✘  {text}{RESET}")

# ─────────────────────────────────────────
#  1. BASIC SET OPERATIONS
# ─────────────────────────────────────────

def set_operations(A: set, B: set, U: set = None) -> dict:
    """
    Perform all standard set operations on A and B.
    U is the universal set (optional, used for complement).
    """
    results = {
        "Union (A ∪ B)"                 : A | B,
        "Intersection (A ∩ B)"          : A & B,
        "Difference (A − B)"            : A - B,
        "Difference (B − A)"            : B - A,
        "Symmetric Difference (A △ B)"  : A ^ B,
    }
    if U is not None:
        results["Complement of A (A')" ] = U - A
        results["Complement of B (B')" ] = U - B
    return results


def display_set_operations(A, B, U=None):
    section("1 · BASIC SET OPERATIONS")
    print(f"  A = {sorted(A)}")
    print(f"  B = {sorted(B)}")
    if U:
        print(f"  U (universal) = {sorted(U)}")
    ops = set_operations(A, B, U)
    for name, result in ops.items():
        print(f"\n  {BOLD}{name}{RESET}")
        print(f"    → {GREEN}{sorted(result)}{RESET}")
    return ops


# ─────────────────────────────────────────
#  2. POWER SET
# ─────────────────────────────────────────

def power_set(S: set) -> list:
    """Return the power set of S as a list of frozensets."""
    S = list(S)
    return [frozenset(combo)
            for r in range(len(S) + 1)
            for combo in combinations(S, r)]


def display_power_set(S):
    section("2 · POWER SET")
    ps = power_set(S)
    print(f"  P({sorted(S)})  — {len(ps)} subsets\n")
    for i, subset in enumerate(ps):
        tag = f"{BLUE}[{i:02d}]{RESET}"
        print(f"    {tag}  {set(subset) if subset else '∅'}")
    info(f"|P(A)| = 2^{len(S)} = {2**len(S)}")
    return ps


# ─────────────────────────────────────────
#  3. CARTESIAN PRODUCT
# ─────────────────────────────────────────

def cartesian_product(A: set, B: set) -> list:
    """Return A × B as a sorted list of (a, b) tuples."""
    return sorted((a, b) for a in A for b in B)


def display_cartesian_product(A, B):
    section("3 · CARTESIAN PRODUCT  A × B")
    cp = cartesian_product(A, B)
    print(f"\n  A × B  ({len(cp)} ordered pairs)\n")
    cols = 4
    for i, pair in enumerate(cp):
        end = "\n" if (i + 1) % cols == 0 else "  "
        print(f"  {GREEN}{pair}{RESET}", end=end)
    if len(cp) % cols != 0:
        print()
    info(f"|A × B| = |A| × |B| = {len(A)} × {len(B)} = {len(cp)}")
    return cp


# ─────────────────────────────────────────
#  4. FORM A RELATION  (user picks pairs)
# ─────────────────────────────────────────

def build_relation_interactive(cp: list) -> set:
    """Let the user select pairs from the Cartesian product to form a relation."""
    section("4 · FORM A RELATION")
    print("\n  Choose pairs from A × B to include in relation R.\n")
    for i, pair in enumerate(cp):
        print(f"    [{i:02d}]  {pair}")

    print("\n  Enter indices separated by spaces  (e.g.  0 2 5 7)")
    print("  Or press ENTER to auto-build a sample relation.\n")
    raw = input("  Your choice: ").strip()

    if raw == "":
        # auto: include pairs where first == second or first < second
        relation = {pair for pair in cp if pair[0] <= pair[1]}
        info("Auto-selected pairs where  a ≤ b")
    else:
        indices = list(map(int, raw.split()))
        relation = {cp[i] for i in indices if 0 <= i < len(cp)}

    print(f"\n  Relation R = {MAGENTA}{sorted(relation)}{RESET}")
    info(f"|R| = {len(relation)} pairs out of {len(cp)} possible")
    return relation


# ─────────────────────────────────────────
#  5. CHECK RELATION PROPERTIES
# ─────────────────────────────────────────

def check_properties(A: set, B: set, R: set) -> dict:
    """
    Check all standard properties of a relation R on A.
    (Assumes R ⊆ A × A for properties like reflexivity.)
    """
    # Only meaningful if A == B (relation on a single set)
    on_single_set = (A == B)
    results = {}

    # ── Reflexive: ∀ a ∈ A, (a,a) ∈ R
    reflexive = all((a, a) in R for a in A)
    results["Reflexive"] = reflexive

    # ── Irreflexive: ∀ a ∈ A, (a,a) ∉ R
    irreflexive = all((a, a) not in R for a in A)
    results["Irreflexive"] = irreflexive

    # ── Symmetric: (a,b) ∈ R → (b,a) ∈ R
    symmetric = all((b, a) in R for (a, b) in R)
    results["Symmetric"] = symmetric

    # ── Antisymmetric: (a,b) ∈ R and (b,a) ∈ R → a == b
    antisymmetric = all(
        a == b
        for (a, b) in R
        if (b, a) in R
    )
    results["Antisymmetric"] = antisymmetric

    # ── Asymmetric: (a,b) ∈ R → (b,a) ∉ R
    asymmetric = all((b, a) not in R for (a, b) in R)
    results["Asymmetric"] = asymmetric

    # ── Transitive: (a,b) ∈ R and (b,c) ∈ R → (a,c) ∈ R
    transitive = all(
        (a, c) in R
        for (a, b1) in R
        for (b2, c) in R
        if b1 == b2
    )
    results["Transitive"] = transitive

    return results


def classify_relation(props: dict) -> str:
    """Give a high-level classification based on properties."""
    p = props
    if p["Reflexive"] and p["Antisymmetric"] and p["Transitive"]:
        return "Partial Order (POSET)"
    if p["Reflexive"] and p["Symmetric"] and p["Transitive"]:
        return "Equivalence Relation"
    if p["Irreflexive"] and p["Asymmetric"] and p["Transitive"]:
        return "Strict Total / Partial Order"
    if p["Symmetric"]:
        return "Symmetric Relation"
    if p["Transitive"]:
        return "Transitive Relation"
    return "General Relation"


def display_properties(A, B, R):
    section("5 · RELATION PROPERTIES")
    props = check_properties(A, B, R)
    print(f"\n  Checking properties for  R = {sorted(R)}\n")
    for name, val in props.items():
        if val:
            ok(f"{name:<20} ✓")
        else:
            warn(f"{name:<20} ✗")
    classification = classify_relation(props)
    print(f"\n  {BOLD}Classification: {CYAN}{classification}{RESET}")
    return props


# ─────────────────────────────────────────
#  6. WARSHALL'S ALGORITHM (Transitive Closure)
# ─────────────────────────────────────────

def warshall(elements: list, R: set) -> tuple:
    """
    Compute the transitive closure of R using Warshall's algorithm.
    Returns (closure_set, step_log).
    """
    n = len(elements)
    idx = {e: i for i, e in enumerate(elements)}

    # Boolean matrix
    M = [[False] * n for _ in range(n)]
    for (a, b) in R:
        if a in idx and b in idx:
            M[idx[a]][idx[b]] = True

    steps = []

    for k in range(n):
        ek = elements[k]
        changed_this_round = []
        for i in range(n):
            for j in range(n):
                if M[i][k] and M[k][j] and not M[i][j]:
                    M[i][j] = True
                    changed_this_round.append(
                        (elements[i], elements[j], ek)
                    )
        steps.append((ek, changed_this_round,
                       [row[:] for row in M]))   # snapshot

    # Convert matrix back to set
    closure = {
        (elements[i], elements[j])
        for i in range(n) for j in range(n) if M[i][j]
    }
    return closure, steps


def print_matrix(elements, M, label="Matrix"):
    n = len(elements)
    print(f"\n    {label}")
    header_row = "      " + "  ".join(f"{str(e):>3}" for e in elements)
    print(f"{BLUE}{header_row}{RESET}")
    for i, ei in enumerate(elements):
        row_str = "  ".join(
            f"{GREEN} 1 {RESET}" if M[i][j] else f"{'':>3}" + "0 "
            for j in range(n)
        )
        print(f"  {BLUE}{str(ei):>3}{RESET}  {row_str}")


def display_warshall(A, R):
    section("6 · WARSHALL'S ALGORITHM  — Transitive Closure")
    elements = sorted(A)

    print(f"\n  Original relation R = {sorted(R)}")
    print(f"  Elements = {elements}\n")

    # Initial matrix
    n = len(elements)
    idx = {e: i for i, e in enumerate(elements)}
    M0 = [[False]*n for _ in range(n)]
    for (a, b) in R:
        if a in idx and b in idx:
            M0[idx[a]][idx[b]] = True
    print_matrix(elements, M0, "Initial Boolean Matrix M⁰")

    closure, steps = warshall(elements, R)

    # Step-by-step output
    for step_i, (pivot, added, snap) in enumerate(steps):
        print(f"\n  {YELLOW}Step k={step_i+1}  (pivot = {pivot}){RESET}")
        if added:
            for (a, c, via) in added:
                print(f"    Added ({a},{c})  via  ({a},{via}) + ({via},{c})")
        else:
            print(f"    No new pairs added.")
        print_matrix(elements, snap, f"M^{step_i+1}")

    print(f"\n  {BOLD}Transitive Closure R⁺ = {CYAN}{sorted(closure)}{RESET}")
    new_pairs = closure - R
    if new_pairs:
        info(f"New pairs added by closure: {sorted(new_pairs)}")
    else:
        info("Relation was already transitively closed.")
    return closure


# ─────────────────────────────────────────
#  7. COUNT POSSIBLE RELATIONS
# ─────────────────────────────────────────

def count_relations(A: set, B: set):
    section("7 · COUNT POSSIBLE RELATIONS")
    cp_size = len(A) * len(B)
    total   = 2 ** cp_size
    print(f"\n  |A × B| = {len(A)} × {len(B)} = {cp_size}")
    print(f"  Total possible relations  = 2^{cp_size} = {total:,}")
    info("Each subset of A × B is a valid binary relation.")

    if A == B:
        n = len(A)
        equiv = count_equivalence_relations(n)
        print(f"\n  Since A = B  (relation on a set of size {n}):")
        info(f"  Equivalence relations (Bell number B_{n}) = {equiv:,}")
    return total


def count_equivalence_relations(n: int) -> int:
    """Bell number B_n using dynamic programming (Bell triangle)."""
    if n == 0: return 1
    B = [[0]*(n+1) for _ in range(n+1)]
    B[0][0] = 1
    for i in range(1, n+1):
        B[i][0] = B[i-1][i-1]
        for j in range(1, i+1):
            B[i][j] = B[i][j-1] + B[i-1][j-1]
    return B[n][0]


# ─────────────────────────────────────────
#  8. REAL-WORLD APPLICATION DEMOS
# ─────────────────────────────────────────

def demo_access_control():
    """Cartesian product → Access-control relation."""
    header("REAL-WORLD DEMO 1 · Access Control System")
    users  = {"Alice", "Bob", "Charlie"}
    perms  = {"Read", "Write", "Delete"}

    print(f"\n  Users       = {sorted(users)}")
    print(f"  Permissions = {sorted(perms)}")

    cp   = cartesian_product(users, perms)
    info(f"All possible user-permission pairs: {len(cp)}")

    # Grant selective permissions
    access = {
        ("Alice",   "Read"),
        ("Alice",   "Write"),
        ("Bob",     "Read"),
        ("Charlie", "Read"),
        ("Charlie", "Write"),
        ("Charlie", "Delete"),
    }
    print(f"\n  Granted access relation  R ⊆ Users × Permissions:\n")
    for user in sorted(users):
        granted = sorted(p for (u, p) in access if u == user)
        print(f"    {user:<10}: {granted}")

    denied = set(cp) - access
    warn(f"Denied pairs ({len(denied)}): {sorted(denied)}")


def demo_social_network():
    """Transitive closure → Friend-of-a-friend reachability."""
    header("REAL-WORLD DEMO 2 · Social Network — Friend Reachability")
    people = {1, 2, 3, 4, 5}
    direct_friends = {(1,2),(2,3),(3,4),(4,5),(2,4)}

    print(f"\n  Direct friendships: {sorted(direct_friends)}")
    closure, _ = warshall(sorted(people), direct_friends)

    print(f"\n  Reachability (transitive closure):")
    for p in sorted(people):
        reachable = sorted(q for (a,b) in closure if a == p for q in [b] if q != p)
        print(f"    Person {p} can reach: {reachable}")
    info("Used in LinkedIn's '2nd degree connection' feature.")


def demo_task_scheduler():
    """Partial order / topological sort via relation properties."""
    header("REAL-WORLD DEMO 3 · Task Scheduler — Dependency Ordering")
    tasks = {"A","B","C","D","E"}
    # Dependency: (x,y) means x must finish before y
    deps = {("A","B"),("A","C"),("B","D"),("C","D"),("D","E")}

    print(f"\n  Tasks = {sorted(tasks)}")
    print(f"  Dependencies (x → y means x before y):")
    for d in sorted(deps):
        print(f"    {d[0]} → {d[1]}")

    closure, _ = warshall(sorted(tasks), deps)
    props = check_properties(tasks, tasks, deps)

    print(f"\n  Transitively closed dependency graph:")
    for t in sorted(tasks):
        must_before = sorted(b for (a,b) in closure if a == t)
        if must_before:
            print(f"    Task {t} must complete before: {must_before}")

    info("Used in Make/CI pipelines and OS process schedulers.")


def demo_database_join():
    """Cartesian product used in SQL JOIN simulation."""
    header("REAL-WORLD DEMO 4 · Database — Simulated SQL JOIN")
    # Simulated tables
    students = {(101,"Alice"),(102,"Bob"),(103,"Charlie")}
    courses  = {(101,"Math"),(101,"CS"),(102,"Physics")}

    print("\n  Students table:  (ID, Name)")
    for s in sorted(students): print(f"    {s}")
    print("\n  Enrollments table:  (StudentID, Course)")
    for c in sorted(courses):  print(f"    {c}")

    # INNER JOIN: student.id == enrollment.student_id
    join_result = {
        (s_id, name, course)
        for (s_id, name) in students
        for (e_id, course) in courses
        if s_id == e_id
    }
    print(f"\n  INNER JOIN result  (ID, Name, Course):")
    for row in sorted(join_result):
        print(f"    {row}")
    info("SQL JOIN = Cartesian Product + Selection Condition (Relation).")


# ─────────────────────────────────────────
#  MAIN DRIVER
# ─────────────────────────────────────────

def get_input_sets():
    header("DISCRETE MATHEMATICS — SET OPERATIONS & CARTESIAN PRODUCT")
    print("""
  This program will:
   1. Perform basic set operations
   2. Generate the power set
   3. Compute the Cartesian product
   4. Form a relation from the product
   5. Check all relation properties
   6. Run Warshall's algorithm (step-by-step)
   7. Count total possible relations
   8. Show real-world application demos
""")
    print("  Enter elements of Set A (space-separated), e.g.  1 2 3")
    raw_A = input("  A = ").strip()
    print("  Enter elements of Set B, e.g.  2 3 4")
    raw_B = input("  B = ").strip()
    print("  Enter universal set U (optional, press ENTER to skip)")
    raw_U = input("  U = ").strip()

    def parse(raw):
        parts = raw.split()
        parsed = []
        for p in parts:
            try:    parsed.append(int(p))
            except: parsed.append(p)
        return set(parsed)

    A = parse(raw_A) if raw_A else {1, 2, 3}
    B = parse(raw_B) if raw_B else {1, 2, 3}
    U = parse(raw_U) if raw_U else None
    return A, B, U


def main():
    A, B, U = get_input_sets()

    # ── Core modules ──
    display_set_operations(A, B, U)
    display_power_set(A)
    cp = display_cartesian_product(A, B)

    R = build_relation_interactive(cp)
    display_properties(A, B, R)

    # Warshall only makes sense when A == B (relation on a set)
    if A == B:
        display_warshall(A, R)
    else:
        section("6 · WARSHALL'S ALGORITHM")
        warn("Warshall's algorithm requires A = B (relation on a single set).")
        info("Running on A only with R ∩ (A×A)…")
        R_restricted = {(a, b) for (a, b) in R if a in A and b in A}
        display_warshall(A, R_restricted)

    count_relations(A, B)

    # ── Real-world demos ──
    section("REAL-WORLD APPLICATIONS")
    choice = input(
        "\n  Run application demos? [y/n] (default y): "
    ).strip().lower()
    if choice != "n":
        demo_access_control()
        demo_social_network()
        demo_task_scheduler()
        demo_database_join()

    header("PROJECT COMPLETE")
    print("""
  Summary of Concepts Demonstrated
  ─────────────────────────────────
   • Set operations (union, ∩, −, △, complement)
   • Power set  — exponential growth 2^n
   • Cartesian product  — foundation of relations
   • Relation  — subset of A × B
   • Properties: reflexive, symmetric, antisymmetric, transitive
   • Warshall's algorithm  — O(n³) transitive closure
   • Bell numbers  — count of equivalence relations
   • Applications: access control, social graphs, task scheduling, SQL
""")


if __name__ == "__main__":
    main()
