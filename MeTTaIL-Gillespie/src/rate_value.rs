//! # Rate Values
//!
//! A `RateValue` is either a real number in [0, 1] (for classical stochastic
//! simulation) or a complex number z such that |z|² ∈ [0, 1] (for quantum
//! model checking via continuous-time Markov chains).
//!
//! The distinction between these two modes determines the entire character
//! of the Gillespie simulator:
//!
//! - **Real**: rates are probabilities; the simulator uses the Stochastic
//!   Simulation Algorithm (SSA) in the style of the stochastic π-machine.
//! - **Complex**: amplitudes interfere; the simulator constructs CTMCs whose
//!   generator matrices have complex entries, enabling quantum model checking.

use num_complex::Complex64;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::fmt;
use thiserror::Error;

/// Errors arising from invalid rate values.
#[derive(Debug, Error)]
pub enum RateValueError {
    #[error("Real rate {0} is not in [0, 1]")]
    RealOutOfRange(f64),

    #[error("Complex amplitude has |z|² = {0}, which is not in [0, 1]")]
    ComplexNormOutOfRange(f64),
}

/// A rate value is either a classical probability or a quantum amplitude.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum RateValue {
    /// A real probability in [0, 1].
    /// Used for stochastic π-machine style Gillespie simulation.
    Real(f64),

    /// A complex amplitude z where |z|² ∈ [0, 1].
    /// Used for quantum model checking via CTMCs.
    Complex(Complex64),
}

// Manual serde: serialize Complex as { "Complex": [re, im] }
impl Serialize for RateValue {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        #[derive(Serialize)]
        enum RateValueProxy {
            Real(f64),
            Complex((f64, f64)),
        }
        let proxy = match self {
            RateValue::Real(r) => RateValueProxy::Real(*r),
            RateValue::Complex(z) => RateValueProxy::Complex((z.re, z.im)),
        };
        proxy.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for RateValue {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        enum RateValueProxy {
            Real(f64),
            Complex((f64, f64)),
        }
        let proxy = RateValueProxy::deserialize(deserializer)?;
        match proxy {
            RateValueProxy::Real(r) => Ok(RateValue::Real(r)),
            RateValueProxy::Complex((re, im)) => {
                Ok(RateValue::Complex(Complex64::new(re, im)))
            }
        }
    }
}

impl RateValue {
    /// Construct a real rate value, validating the range.
    pub fn real(r: f64) -> Result<Self, RateValueError> {
        if r < 0.0 || r > 1.0 {
            Err(RateValueError::RealOutOfRange(r))
        } else {
            Ok(RateValue::Real(r))
        }
    }

    /// Construct a complex rate value, validating |z|² ∈ [0, 1].
    pub fn complex(re: f64, im: f64) -> Result<Self, RateValueError> {
        let z = Complex64::new(re, im);
        let norm_sq = z.norm_sqr();
        if norm_sq < 0.0 || norm_sq > 1.0 + 1e-10 {
            Err(RateValueError::ComplexNormOutOfRange(norm_sq))
        } else {
            Ok(RateValue::Complex(z))
        }
    }

    /// Construct a complex rate value from a `Complex64` directly.
    pub fn from_complex(z: Complex64) -> Result<Self, RateValueError> {
        let norm_sq = z.norm_sqr();
        if norm_sq > 1.0 + 1e-10 {
            Err(RateValueError::ComplexNormOutOfRange(norm_sq))
        } else {
            Ok(RateValue::Complex(z))
        }
    }

    /// Returns true if this is a real-valued rate.
    pub fn is_real(&self) -> bool {
        matches!(self, RateValue::Real(_))
    }

    /// Returns true if this is a complex-valued amplitude.
    pub fn is_complex(&self) -> bool {
        matches!(self, RateValue::Complex(_))
    }

    /// Extract the effective probability (rate for SSA, |z|² for quantum).
    pub fn probability(&self) -> f64 {
        match self {
            RateValue::Real(r) => *r,
            RateValue::Complex(z) => z.norm_sqr(),
        }
    }

    /// For quantum mode: get the complex amplitude.
    /// For real mode: returns `z = r + 0i`.
    pub fn as_complex(&self) -> Complex64 {
        match self {
            RateValue::Real(r) => Complex64::new(*r, 0.0),
            RateValue::Complex(z) => *z,
        }
    }

    /// Multiply two rate values.
    /// Real * Real → Real; anything involving Complex → Complex.
    pub fn compose(&self, other: &RateValue) -> Result<RateValue, RateValueError> {
        match (self, other) {
            (RateValue::Real(a), RateValue::Real(b)) => RateValue::real(a * b),
            _ => {
                let z = self.as_complex() * other.as_complex();
                RateValue::from_complex(z)
            }
        }
    }

    /// Add two rate values (for combining parallel transition rates).
    pub fn add(&self, other: &RateValue) -> RateValue {
        match (self, other) {
            (RateValue::Real(a), RateValue::Real(b)) => {
                // Clamp to [0, 1] for safety in additive contexts
                RateValue::Real((a + b).min(1.0))
            }
            _ => {
                let z = self.as_complex() + other.as_complex();
                RateValue::Complex(z)
            }
        }
    }
}

impl fmt::Display for RateValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RateValue::Real(r) => write!(f, "{:.6}", r),
            RateValue::Complex(z) => {
                if z.im >= 0.0 {
                    write!(f, "{:.6}+{:.6}i", z.re, z.im)
                } else {
                    write!(f, "{:.6}{:.6}i", z.re, z.im)
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_real_rate_valid() {
        assert!(RateValue::real(0.0).is_ok());
        assert!(RateValue::real(0.5).is_ok());
        assert!(RateValue::real(1.0).is_ok());
    }

    #[test]
    fn test_real_rate_invalid() {
        assert!(RateValue::real(-0.1).is_err());
        assert!(RateValue::real(1.1).is_err());
    }

    #[test]
    fn test_complex_amplitude_valid() {
        // |0.5 + 0.5i|² = 0.5
        assert!(RateValue::complex(0.5, 0.5).is_ok());
        // |1/√2 + 0i|² = 0.5
        let s = 1.0_f64 / 2.0_f64.sqrt();
        assert!(RateValue::complex(s, 0.0).is_ok());
    }

    #[test]
    fn test_complex_amplitude_invalid() {
        // |1 + 1i|² = 2, out of range
        assert!(RateValue::complex(1.0, 1.0).is_err());
    }

    #[test]
    fn test_probability() {
        let r = RateValue::real(0.3).unwrap();
        assert!((r.probability() - 0.3).abs() < 1e-10);

        let c = RateValue::complex(0.5, 0.5).unwrap();
        assert!((c.probability() - 0.5).abs() < 1e-10);
    }

    #[test]
    fn test_compose() {
        let a = RateValue::real(0.5).unwrap();
        let b = RateValue::real(0.4).unwrap();
        let c = a.compose(&b).unwrap();
        assert!((c.probability() - 0.2).abs() < 1e-10);
    }
}
