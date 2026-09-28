use crate::alpha_match::*;
use crate::utils::*;
use regex::Regex;
use std::collections::VecDeque;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
type DependencyGraph = BTreeMap<String, BTreeSet<String>>;
type FormulaMap = BTreeMap<String, String>;

/// Parse DAG from file
pub fn load_dag(dag_file: &str) -> DependencyGraph {
    let content = fs::read_to_string(dag_file).expect("Failed to read DAG file");
    let re = Regex::new(r"^\s*(\S+)\s*->\s*\{([^}]*)\}").unwrap();
    let mut dag = BTreeMap::new();
    for line in content.lines() {
        if let Some(cap) = re.captures(line) {
            let parent = cap[1].to_string();
            let children_str = cap[2].trim();
            let mut children = BTreeSet::new();
            if !children_str.is_empty() {
                for c in children_str.split(',') {
                    children.insert(c.trim().trim_matches('"').to_string());
                }
            }
            dag.insert(parent, children);
        }
    }
    dag
}

/// Write DAG to file
pub fn write_dag(dag_file: &str, dag: &DependencyGraph) -> Result<(), std::io::Error> {
    let mut output = String::new();
    for (parent, children) in dag.iter() {
        let children_str = children
            .iter()
            .map(|c| format!("\"{}\"", c))
            .collect::<Vec<_>>()
            .join(", ");

        output.push_str(&format!("{parent} -> {{{children_str}}}\n"));
    }
    fs::write(dag_file, output)
}

/// Build DAG from precomputed lemmas
pub fn build_dag(
    root_lemma: &str,
    precomputed: &PrecomputedLemmas,
) -> Result<(DependencyGraph, FormulaMap), String> {
    let PrecomputedLemmas {
        all_lemmas,
        all_twee,
        lemmas,
    } = precomputed;

    // build DAG
    let mut dag: DependencyGraph = BTreeMap::new();
    let mut duplicates: Vec<(String, String)> = Vec::new();
    let mut queue: VecDeque<String> = VecDeque::new();
    let mut seen: BTreeSet<String> = BTreeSet::new();

    queue.push_back(root_lemma.to_string());

    while let Some(lemma) = queue.pop_front() {
        // built-in axiom
        if is_builtin_axiom(&lemma) {
            continue;
        }
        // conjecture dependency
        if lemma.starts_with("conjecture_") {
            continue;
        }
        if seen.contains(&lemma) {
            continue;
        }
        seen.insert(lemma.clone());

        let lemma_info = all_lemmas
            .get(&lemma)
            .ok_or_else(|| format!("Lemma {} not found in precomputed lemmas", lemma))?;

        dag.entry(lemma.clone()).or_default();

        // check if the lemma itself is a duplicate of a TWEE lemma
        let mut redirected = false;
        for twee_dep in all_twee {
            let twee_name = &twee_dep.name;
            let twee_formula = &twee_dep.formula;
            if formulas_match(&lemma_info.formula, twee_formula)
                && formulas_match(twee_formula, &lemma_info.formula)
            {
                crate::klog_debug!("[DUPLICATE] lemma {} duplicates {}", lemma, twee_name);
                duplicates.push((lemma.clone(), twee_name.clone()));

                // redirect to smallest parent
                let smallest_parent = twee_dep
                    .parents
                    .iter()
                    .min_by_key(|p| {
                        p.chars()
                            .filter(|c| c.is_ascii_digit())
                            .collect::<String>()
                            .parse::<u32>()
                            .unwrap_or(u32::MAX)
                    })
                    .expect("Duplicate TWEE lemma has no parents");

                // add DAG edges
                // get the dependencies of the smallest parent
                if let Some(parent_info) = all_lemmas.get(smallest_parent) {
                    dag.entry(smallest_parent.clone()).or_default().extend(
                        parent_info
                            .dependencies
                            .iter()
                            .map(|(dep_name, _)| dep_name.clone()),
                    );
                }

                queue.push_back(smallest_parent.clone());
                redirected = true;
                break;
            }
        }

        // handle dependencies
        for (dep_name, dep_formula) in &lemma_info.dependencies {
            if dep_name.starts_with("twee_") {
                continue;
            } // skip twee dependencies

            let mut is_duplicate = false;
            for twee_dep in all_twee {
                let twee_name = &twee_dep.name;
                let twee_formula = &twee_dep.formula;
                if formulas_match(dep_formula, twee_formula)
                    && formulas_match(twee_formula, dep_formula)
                {
                    crate::klog_debug!("[DUPLICATE] dep {} duplicates {}", dep_name, twee_name);
                    duplicates.push((dep_name.clone(), twee_name.clone()));
                    is_duplicate = true;

                    // redirect DAG edges to the smallest parent
                    let smallest_parent = twee_dep
                        .parents
                        .iter()
                        .min_by_key(|p| {
                            p.chars()
                                .filter(|c| c.is_ascii_digit())
                                .collect::<String>()
                                .parse::<u32>()
                                .unwrap_or(u32::MAX)
                        })
                        .expect("TWEE dep has no parents");

                    // get the dependencies of the smallest parent
                    if let Some(parent_info) = all_lemmas.get(smallest_parent) {
                        dag.entry(smallest_parent.clone()).or_default().extend(
                            parent_info
                                .dependencies
                                .iter()
                                .map(|(dep_name, _)| dep_name.clone()),
                        );
                    }

                    // continue traversal from parent
                    if !seen.contains(smallest_parent) {
                        queue.push_back(smallest_parent.clone());
                    }
                    break;
                }
            }

            if !is_duplicate && !redirected {
                // normal DAG entry
                dag.entry(lemma.clone())
                    .or_default()
                    .insert(dep_name.clone());

                // also add all dependencies of this dep, if available
                if let Some(dep_info) = all_lemmas.get(dep_name) {
                    dag.entry(dep_name.clone())
                        .or_default()
                        .extend(dep_info.dependencies.iter().map(|(child, _)| child.clone()));
                }

                if !seen.contains(dep_name) {
                    queue.push_back(dep_name.clone());
                }
            }
        }
    }

    Ok((dag, lemmas.clone()))
}
