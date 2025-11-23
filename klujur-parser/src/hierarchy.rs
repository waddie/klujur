// klujur-parser - Hierarchy type for ad-hoc taxonomies
// Copyright (c) 2025 Tom Waddington. MIT licensed.

//! Clojure-style hierarchy for type relationships used in multimethod dispatch.

// Allow mutable key types - KlujurVal has interior mutability for Vars/Atoms by design
#![allow(clippy::mutable_key_type)]

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::KlujurVal;

// ============================================================================
// Hierarchy Type
// ============================================================================

/// A Clojure-style hierarchy for type relationships.
///
/// Hierarchies support ad-hoc taxonomies where relationships between values
/// can be established at runtime using `derive`. The `isa?` function can then
/// query these relationships, and multimethods can use them for dispatch.
#[derive(Clone, Default)]
pub struct KlujurHierarchy {
    /// Direct parent relationships: child -> set of direct parents
    parents: HashMap<KlujurVal, HashSet<KlujurVal>>,
    /// Cached transitive ancestors: child -> set of all ancestors
    ancestors: HashMap<KlujurVal, HashSet<KlujurVal>>,
    /// Cached transitive descendants: parent -> set of all descendants
    descendants: HashMap<KlujurVal, HashSet<KlujurVal>>,
}

impl KlujurHierarchy {
    /// Create a new empty hierarchy.
    pub fn new() -> Self {
        KlujurHierarchy {
            parents: HashMap::new(),
            ancestors: HashMap::new(),
            descendants: HashMap::new(),
        }
    }

    /// Establish a parent/child relationship.
    ///
    /// Creates a relationship where `child` derives from `parent`.
    /// Returns an error if this would create a cycle.
    pub fn derive(&mut self, child: KlujurVal, parent: KlujurVal) -> Result<(), String> {
        // Check for self-derivation
        if child == parent {
            return Err(format!("Cannot derive {:?} from itself", child));
        }

        // Check for cycle: if parent already derives from child
        if self.isa(&parent, &child) {
            return Err(format!(
                "Cyclic derivation: {:?} already derives from {:?}",
                parent, child
            ));
        }

        // Add direct parent relationship
        self.parents
            .entry(child.clone())
            .or_default()
            .insert(parent.clone());

        // Recompute transitive closures
        self.update_ancestors(&child);
        self.update_descendants(&parent);

        Ok(())
    }

    /// Remove a parent/child relationship.
    pub fn underive(&mut self, child: &KlujurVal, parent: &KlujurVal) {
        if let Some(parents) = self.parents.get_mut(child) {
            parents.remove(parent);
            if parents.is_empty() {
                self.parents.remove(child);
            }
        }

        // Recompute transitive closures (expensive but correct)
        self.recompute_all_caches();
    }

    /// Check if child derives from (is-a) parent.
    ///
    /// Returns true if:
    /// - child == parent (reflexive)
    /// - child has parent as a direct parent
    /// - child has parent as an ancestor (transitively)
    pub fn isa(&self, child: &KlujurVal, parent: &KlujurVal) -> bool {
        if child == parent {
            return true;
        }

        self.ancestors
            .get(child)
            .map(|a| a.contains(parent))
            .unwrap_or(false)
    }

    /// Get direct parents of a value.
    pub fn parents(&self, child: &KlujurVal) -> HashSet<KlujurVal> {
        self.parents.get(child).cloned().unwrap_or_default()
    }

    /// Get all ancestors of a value (transitive closure of parents).
    pub fn ancestors(&self, child: &KlujurVal) -> HashSet<KlujurVal> {
        self.ancestors.get(child).cloned().unwrap_or_default()
    }

    /// Get all descendants of a value (transitive closure of children).
    pub fn descendants(&self, parent: &KlujurVal) -> HashSet<KlujurVal> {
        self.descendants.get(parent).cloned().unwrap_or_default()
    }

    /// Update ancestors cache for a child and all its descendants.
    fn update_ancestors(&mut self, child: &KlujurVal) {
        let mut ancestors = HashSet::new();

        // Collect all direct parents and their ancestors
        if let Some(direct_parents) = self.parents.get(child) {
            for parent in direct_parents.iter() {
                ancestors.insert(parent.clone());
                if let Some(parent_ancestors) = self.ancestors.get(parent) {
                    ancestors.extend(parent_ancestors.iter().cloned());
                }
            }
        }

        if ancestors.is_empty() {
            self.ancestors.remove(child);
        } else {
            self.ancestors.insert(child.clone(), ancestors);
        }

        // Update descendants of this child (they inherit our new ancestors)
        let children: Vec<_> = self
            .parents
            .iter()
            .filter(|(_, ps)| ps.contains(child))
            .map(|(c, _)| c.clone())
            .collect();

        for c in children {
            self.update_ancestors(&c);
        }
    }

    /// Update descendants cache for a parent and all its ancestors.
    fn update_descendants(&mut self, parent: &KlujurVal) {
        let mut descendants = HashSet::new();

        // Collect all direct children
        for (child, parents) in &self.parents {
            if parents.contains(parent) {
                descendants.insert(child.clone());
                // Also include all descendants of direct children
                if let Some(child_descendants) = self.descendants.get(child) {
                    descendants.extend(child_descendants.iter().cloned());
                }
            }
        }

        if descendants.is_empty() {
            self.descendants.remove(parent);
        } else {
            self.descendants.insert(parent.clone(), descendants);
        }

        // Update ancestors of this parent (they gain our descendants)
        if let Some(parent_ancestors) = self.ancestors.get(parent).cloned() {
            for ancestor in parent_ancestors {
                self.update_descendants(&ancestor);
            }
        }
    }

    /// Recompute all caches from scratch (used after underive).
    fn recompute_all_caches(&mut self) {
        self.ancestors.clear();
        self.descendants.clear();

        // Topological order: process nodes with no parents first
        let mut processed: HashSet<KlujurVal> = HashSet::new();
        let all_nodes: HashSet<_> = self
            .parents
            .keys()
            .chain(self.parents.values().flat_map(|s| s.iter()))
            .cloned()
            .collect();

        // Keep processing until all nodes are done
        let mut changed = true;
        while changed {
            changed = false;
            for node in &all_nodes {
                if processed.contains(node) {
                    continue;
                }

                // Check if all parents are processed
                let parents = self.parents.get(node);
                let all_parents_processed = parents
                    .map(|ps| {
                        ps.iter()
                            .all(|p| processed.contains(p) || !all_nodes.contains(p))
                    })
                    .unwrap_or(true);

                if all_parents_processed {
                    // Compute ancestors for this node
                    let mut ancestors = HashSet::new();
                    if let Some(direct_parents) = self.parents.get(node) {
                        for parent in direct_parents.iter() {
                            ancestors.insert(parent.clone());
                            if let Some(parent_ancestors) = self.ancestors.get(parent) {
                                ancestors.extend(parent_ancestors.iter().cloned());
                            }
                        }
                    }
                    if !ancestors.is_empty() {
                        self.ancestors.insert(node.clone(), ancestors);
                    }

                    processed.insert(node.clone());
                    changed = true;
                }
            }
        }

        // Recompute descendants from ancestors
        for (child, ancs) in &self.ancestors {
            for ancestor in ancs {
                self.descendants
                    .entry(ancestor.clone())
                    .or_default()
                    .insert(child.clone());
            }
        }
    }

    /// Find the best matching method in a multimethod for a dispatch value,
    /// considering hierarchy relationships and preferences.
    ///
    /// Returns the method and the dispatch value it matched on.
    pub fn find_best_method(
        &self,
        dispatch_val: &KlujurVal,
        methods: &HashMap<KlujurVal, KlujurVal>,
        preferences: &HashMap<(KlujurVal, KlujurVal), bool>,
    ) -> Option<(KlujurVal, KlujurVal)> {
        // First try exact match
        if let Some(method) = methods.get(dispatch_val) {
            return Some((dispatch_val.clone(), method.clone()));
        }

        // Collect all matching ancestors
        let mut candidates: Vec<(KlujurVal, KlujurVal)> = Vec::new();
        if let Some(ancestors) = self.ancestors.get(dispatch_val) {
            for ancestor in ancestors {
                if let Some(method) = methods.get(ancestor) {
                    candidates.push((ancestor.clone(), method.clone()));
                }
            }
        }

        match candidates.len() {
            0 => None,
            1 => Some(candidates.into_iter().next().unwrap()),
            _ => {
                // Multiple matches - use preferences to disambiguate
                // Find the most specific (most derived) matching dispatch value
                let mut best: Option<(KlujurVal, KlujurVal)> = None;

                for (dv, method) in &candidates {
                    let dominated = candidates.iter().any(|(other_dv, _)| {
                        if other_dv == dv {
                            return false;
                        }
                        // Check if other_dv is more specific (derives from dv)
                        if self.isa(other_dv, dv) {
                            // other_dv is more specific
                            // Unless we prefer dv over other_dv
                            !preferences.contains_key(&(dv.clone(), other_dv.clone()))
                        } else if preferences.contains_key(&(other_dv.clone(), dv.clone())) {
                            // Explicit preference for other_dv
                            true
                        } else {
                            false
                        }
                    });

                    if !dominated {
                        if best.is_some() {
                            // Ambiguous: multiple non-dominated candidates
                            // In Clojure this throws, but we'll pick one
                            // (The first one found)
                            continue;
                        }
                        best = Some((dv.clone(), method.clone()));
                    }
                }

                best.or_else(|| candidates.into_iter().next())
            }
        }
    }
}

impl fmt::Debug for KlujurHierarchy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#<Hierarchy: {} relationships>", self.parents.len())
    }
}

impl fmt::Display for KlujurHierarchy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#<Hierarchy: {} relationships>", self.parents.len())
    }
}

impl PartialEq for KlujurHierarchy {
    fn eq(&self, other: &Self) -> bool {
        self.parents == other.parents
    }
}

impl Eq for KlujurHierarchy {}
