"""Summarize actual Lean dependency paths for the four paper-facing entry points.

Run from lean/ after building and running scripts/AuditCorrespondence.lean.
Only the standard library is used. This checks dependency evidence, not the
mathematical equivalence of prose and formal statements.
"""

import argparse
import collections
import hashlib
import json
import pathlib


def dependency_paths(nodes, root):
    previous = {root: None}
    queue = collections.deque([root])
    while queue:
        name = queue.popleft()
        node = nodes[name]
        values = set(node["valueDependencies"])
        for dep in sorted(values | set(node["typeDependencies"])):
            if dep not in nodes:
                raise ValueError(f"Unresolved project dependency: {dep}")
            if dep not in previous:
                previous[dep] = (name, "value" if dep in values else "type")
                queue.append(dep)
    return previous


def witness(previous, target):
    if target not in previous:
        return None
    path = [target]
    kinds = []
    while previous[path[-1]] is not None:
        parent, kind = previous[path[-1]]
        path.append(parent)
        kinds.append(kind)
    return {"path": path[::-1], "edgeKinds": kinds[::-1]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--graph", type=pathlib.Path,
                        default=pathlib.Path(".lake/proof-correspondence-full.json"))
    parser.add_argument("--output", type=pathlib.Path,
                        default=pathlib.Path("../docs/audits/proof-correspondence.json"))
    parser.add_argument("--revision", required=True,
                        help="Git revision independently verified before the audit")
    args = parser.parse_args()
    if len(args.revision) != 40 or any(c not in "0123456789abcdef" for c in args.revision):
        raise ValueError("Expected the full lowercase Git revision")
    repo = pathlib.Path(__file__).resolve().parents[2]
    raw = json.loads(args.graph.read_text(encoding="utf-8-sig"))
    nodes = {item["name"]: item for item in raw["declarations"]}
    targets = [
        "SSPRK.rkP_substochastic",
        "SSPRK.rkN_nonneg",
        "SSPRK.rkOmega_N_ones_eq",
        "SSPRK.rkOmega_N_sq_ones_eq",
        "SSPRK.rkOmega_N_cu_ones_eq",
        "SSPRK.exists_variance_potential",
        "SSPRK.phase_variance_pointwise_of_potential",
        "SSPRK.phase_second_moment_bound",
        "SSPRK.phase_mixture_chain_classification_of_pos",
        "SSPRK.AbsolutelyMonotoneAt.phaseType",
        "SSPRK.PhaseTypeData.third_moment_lower_bound",
        "SSPRK.PhaseTypeData.green_moment_class",
        "SSPRK.PhaseTypeData.green_zero_momentClass_of_induction",
        "SSPRK.PhaseTypeData.eliminateZero",
        "SSPRK.PhaseTypeData.normalizedGreen",
        "SSPRK.phaseBlock_third_moment",
        "SSPRK.MomentClass.add",
        "SSPRK.MomentClass.finite_mixture",
        "SSPRK.length_biased_component_bound",
        "SSPRK.auxiliary_moment_class",
        "SSPRK.PhaseTypeData.normalized_independent_replacement",
        "SSPRK.lengthBias_normalized_variance",
        "SSPRK.lengthBias_independentSumLaw",
        "SSPRK.lengthBias_probabilityMomentMixture",
        "SSPRK.PhaseTypeData.canonicalRecords_map_occupationRest",
        "SSPRK.PhaseTypeData.canonicalRecords_map_absorptionTime",
        "SSPRK.PhaseTypeData.third_equality_representation",
        "SSPRK.PhaseTypeData.green_mixture_second_eq_of_third_eq",
        "SSPRK.PhaseTypeData.green_second_eq_of_third_eq",
        "SSPRK.PhaseTypeData.third_integral_eq_iff_cond_erlang",
        "SSPRK.PhaseTypeData.erlang_rigidity_of_measure_eq_gamma",
        "SSPRK.PhaseTypeData.erlang_rigidity_of_num_phases_le",
        "SSPRK.absolutelyMonotoneAt_absoluteMonotonicityRadius",
        "SSPRK.eq_midpoint_of_sorted_transform",
        "SSPRK.eq_sdirk_of_sorted_transform",
        "SSPRK.second_order_classification_at_bound",
        "SSPRK.third_order_classification_at_bound",
        "SSPRK.PhaseTypeData.normalizeInitial_integral_pow",
        "SSPRK.PhaseTypeData.cond_positive_eq_normalizeInitial",
    ]
    supplementary = [
        "SSPRK.second_order_radius_bound",
        "SSPRK.third_order_radius_bound",
        "SSPRK.second_order_optimal_radius",
        "SSPRK.third_order_optimal_radius",
        "SSPRK.second_order_unique_of_radius_eq",
        "SSPRK.third_order_unique_of_radius_eq",
    ]
    missing = sorted(set(targets + supplementary) - nodes.keys())
    if missing:
        raise ValueError(f"Named audit declarations are missing: {missing}")
    analyses = []
    for root in [item["name"] for item in raw["roots"]] + supplementary:
        previous = dependency_paths(nodes, root)
        analyses.append({
            "root": root,
            "reachableProjectConstantsIncludingRoot": len(previous),
            "queries": {target: witness(previous, target) for target in targets},
        })
    modules = sorted({item["module"] for item in nodes.values()})
    sources = {}
    for module in modules:
        path = pathlib.PurePosixPath("lean", *module.split(".")).with_suffix(".lean")
        content = (repo / path).read_text(encoding="utf-8")
        sources[str(path)] = hashlib.sha256(content.encode("utf-8")).hexdigest()
    used = set(targets + supplementary + [item["name"] for item in raw["roots"]])
    for analysis in analyses:
        for evidence in analysis["queries"].values():
            if evidence is not None:
                used.update(evidence["path"])
    output = {
        "sourceRevision": args.revision,
        "paper": "docs/V1.6.pdf",
        "paperSha256": hashlib.sha256((repo / "docs/V1.6.pdf").read_bytes()).hexdigest(),
        "leanToolchain": (repo / "lean/lean-toolchain").read_text().strip(),
        "graphSemantics": "Project-owned constants in elaborated types and values; "
                          "value edges preferred when both kinds exist; null means no path.",
        "limits": "Not a semantic equivalence certificate. Imports and existence alone "
                  "are not proof-route evidence. Build before generating the graph.",
        "projectDeclarations": len(nodes),
        "coreEntries": raw["roots"],
        "analyses": analyses,
        "witnessNodes": {name: nodes[name] for name in sorted(used)},
        "sourceSha256LfNormalized": sources,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, ensure_ascii=False, indent=2) + "\n",
                           encoding="utf-8")
    for analysis in analyses[:4]:
        print(analysis["root"], analysis["reachableProjectConstantsIncludingRoot"])
    print(f"Wrote {args.output}")


if __name__ == "__main__":
    main()
