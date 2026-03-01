//! # Spatial Behavior Terms
//!
//! A `SpatialBehavior` term refines the type of the left-hand side of a
//! rewrite rule. These terms describe *how* a term participates in spatial
//! structure — locality, mobility, proximity — which is exactly the kind of
//! information needed to assign rates to transitions in a stochastic or
//! quantum simulation.
//!
//! In the rho-calculus / rholang setting, spatial behaviors arise naturally
//! from the concurrent structure: processes communicate on named channels,
//! and the spatial behavior describes the communication topology.
//!
//! ## Examples of spatial behaviors:
//!
//! - **Local(channel)**: the transition is localized to a specific channel
//! - **Parallel(behaviors)**: concurrent composition of spatial behaviors
//! - **Sequential(b1, b2)**: b1 happens then b2
//! - **Guard(condition)**: gated by a spatial condition
//! - **Replicated(behavior)**: persistent/replicated behavior
//! - **Null**: no spatial refinement (the trivial behavior)

use serde::{Deserialize, Serialize};
use std::fmt;

/// A unique identifier for a channel/name in the rholang sense.
/// In the full integration this would be a `Name` from the generated AST,
/// but here we keep it abstract for the extension crate.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ChannelId(pub String);

impl ChannelId {
    pub fn new(s: impl Into<String>) -> Self {
        ChannelId(s.into())
    }
}

impl fmt::Display for ChannelId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "@{}", self.0)
    }
}

/// A spatial behavior term that refines the type on the LHS of a rewrite rule.
///
/// These serve as the **keys** in rate maps. Each spatial behavior describes
/// a different mode of interaction, and the associated rate value determines
/// how likely (or with what amplitude) that mode fires.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SpatialBehavior {
    /// No spatial refinement — the trivial/default behavior.
    Null,

    /// Localized to a specific channel.
    /// In the stochastic π-machine, this is a communication on channel `n`.
    Local(ChannelId),

    /// Communication between two channels — an interaction.
    /// This refines the COMM rule in rholang: `n?(x).P | n!(Q)`.
    Interaction {
        input_channel: ChannelId,
        output_channel: ChannelId,
    },

    /// Parallel composition of spatial behaviors.
    /// Rate for the composite is the product of component rates.
    Parallel(Vec<SpatialBehavior>),

    /// Sequential composition: first behavior enables the second.
    Sequential(Box<SpatialBehavior>, Box<SpatialBehavior>),

    /// Guarded behavior — gated by a spatial predicate.
    /// The guard is represented as a string expression for now;
    /// in the full integration this would be a term in the defined language.
    Guard {
        condition: String,
        body: Box<SpatialBehavior>,
    },

    /// Replicated behavior — persistent, as in `!P` in rholang.
    /// The rate applies to each individual firing.
    Replicated(Box<SpatialBehavior>),

    /// A user-defined spatial behavior with a symbolic tag.
    /// This allows language definitions to introduce domain-specific
    /// spatial refinements.
    Custom {
        tag: String,
        children: Vec<SpatialBehavior>,
    },
}

impl SpatialBehavior {
    /// Create a null (trivial) spatial behavior.
    pub fn null() -> Self {
        SpatialBehavior::Null
    }

    /// Create a local behavior on a channel.
    pub fn local(channel: impl Into<String>) -> Self {
        SpatialBehavior::Local(ChannelId::new(channel))
    }

    /// Create an interaction between two channels.
    pub fn interaction(input: impl Into<String>, output: impl Into<String>) -> Self {
        SpatialBehavior::Interaction {
            input_channel: ChannelId::new(input),
            output_channel: ChannelId::new(output),
        }
    }

    /// Parallel composition of behaviors.
    pub fn par(behaviors: Vec<SpatialBehavior>) -> Self {
        SpatialBehavior::Parallel(behaviors)
    }

    /// Sequential composition.
    pub fn seq(first: SpatialBehavior, second: SpatialBehavior) -> Self {
        SpatialBehavior::Sequential(Box::new(first), Box::new(second))
    }

    /// A replicated behavior.
    pub fn replicated(inner: SpatialBehavior) -> Self {
        SpatialBehavior::Replicated(Box::new(inner))
    }

    /// Test whether this is the null behavior.
    pub fn is_null(&self) -> bool {
        matches!(self, SpatialBehavior::Null)
    }

    /// Collect all channel IDs referenced by this behavior.
    pub fn channels(&self) -> Vec<&ChannelId> {
        match self {
            SpatialBehavior::Null => vec![],
            SpatialBehavior::Local(ch) => vec![ch],
            SpatialBehavior::Interaction {
                input_channel,
                output_channel,
            } => vec![input_channel, output_channel],
            SpatialBehavior::Parallel(bs) => bs.iter().flat_map(|b| b.channels()).collect(),
            SpatialBehavior::Sequential(a, b) => {
                let mut chs = a.channels();
                chs.extend(b.channels());
                chs
            }
            SpatialBehavior::Guard { body, .. } => body.channels(),
            SpatialBehavior::Replicated(inner) => inner.channels(),
            SpatialBehavior::Custom { children, .. } => {
                children.iter().flat_map(|c| c.channels()).collect()
            }
        }
    }
}

impl fmt::Display for SpatialBehavior {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SpatialBehavior::Null => write!(f, "∅"),
            SpatialBehavior::Local(ch) => write!(f, "local({})", ch),
            SpatialBehavior::Interaction {
                input_channel,
                output_channel,
            } => write!(f, "comm({}, {})", input_channel, output_channel),
            SpatialBehavior::Parallel(bs) => {
                let strs: Vec<_> = bs.iter().map(|b| b.to_string()).collect();
                write!(f, "({})", strs.join(" | "))
            }
            SpatialBehavior::Sequential(a, b) => write!(f, "({} ; {})", a, b),
            SpatialBehavior::Guard { condition, body } => {
                write!(f, "[{}]({})", condition, body)
            }
            SpatialBehavior::Replicated(inner) => write!(f, "!{}", inner),
            SpatialBehavior::Custom { tag, children } => {
                if children.is_empty() {
                    write!(f, "{}", tag)
                } else {
                    let strs: Vec<_> = children.iter().map(|c| c.to_string()).collect();
                    write!(f, "{}({})", tag, strs.join(", "))
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_spatial_display() {
        let sb = SpatialBehavior::interaction("x", "y");
        assert_eq!(sb.to_string(), "comm(@x, @y)");
    }

    #[test]
    fn test_channels_collection() {
        let sb = SpatialBehavior::par(vec![
            SpatialBehavior::local("a"),
            SpatialBehavior::interaction("b", "c"),
        ]);
        let chs: Vec<String> = sb.channels().iter().map(|c| c.0.clone()).collect();
        assert_eq!(chs, vec!["a", "b", "c"]);
    }

    #[test]
    fn test_replicated() {
        let sb = SpatialBehavior::replicated(SpatialBehavior::local("x"));
        assert_eq!(sb.to_string(), "!local(@x)");
    }
}
