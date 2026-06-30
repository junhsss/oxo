use std::time::{Duration, Instant};

use crate::logic::{
    countdown_bytes, countdown_step_facts, loop_capstone, loop_capstone_gen, mem_of_bytes,
    numerals_sig,
};
use crate::{check, eval, infer, Context, Term};

pub struct CountdownCertificate {
    pub bytes: Vec<u8>,
    pub program_logic: (Term, Term),
    pub final_theorem: (Term, Term),
}

#[derive(Debug)]
pub struct RecheckReport {
    pub certified: Term,
    pub binary_facts: Duration,
    pub program_logic: Duration,
    pub instantiation: Duration,
    pub n_decode_facts: usize,
    pub bytes_match_canonical: bool,
}

impl CountdownCertificate {
    pub fn produce() -> Self {
        CountdownCertificate {
            bytes: countdown_bytes(),
            program_logic: loop_capstone_gen(),
            final_theorem: loop_capstone(),
        }
    }

    pub fn recheck(&self) -> Result<RecheckReport, String> {
        let sig = numerals_sig();
        let ctx = Context::with_sig(sig.clone());
        let kcheck = |proof: &Term, prop: &Term| -> Result<(), String> {
            infer(&ctx, proof)?;
            check(&ctx, proof, &eval(&sig, &Vec::new(), prop))
        };

        let t = Instant::now();
        let facts = countdown_step_facts(mem_of_bytes(&self.bytes));
        let n_decode_facts = facts.len();
        for (i, (ty, prover)) in facts.iter().enumerate() {
            kcheck(prover, ty).map_err(|e| format!("binary-tied fact {i} rejected: {e}"))?;
        }
        let binary_facts = t.elapsed();

        let t = Instant::now();
        let (pl_prop, pl_proof) = &self.program_logic;
        kcheck(pl_proof, pl_prop).map_err(|e| format!("program logic rejected: {e}"))?;
        let program_logic = t.elapsed();

        let t = Instant::now();
        let (ft_prop, ft_proof) = &self.final_theorem;
        infer(&ctx, ft_proof).map_err(|e| format!("instantiation rejected: {e}"))?;
        let instantiation = t.elapsed();

        Ok(RecheckReport {
            certified: ft_prop.clone(),
            binary_facts,
            program_logic,
            instantiation,
            n_decode_facts,
            bytes_match_canonical: self.bytes == countdown_bytes(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::logic::step;

    #[test]
    fn countdown_certificate_rechecks() {
        let cert = CountdownCertificate::produce();
        let report = cert.recheck().expect("honest certificate must re-check");
        assert!(report.bytes_match_canonical);
        assert_eq!(report.n_decode_facts, 4);
        assert_eq!(report.certified, cert.final_theorem.0);
        eprintln!(
            "recheck (off-TCB): binary_facts={:?}  program_logic={:?}  instantiation={:?}",
            report.binary_facts, report.program_logic, report.instantiation
        );
    }

    #[test]
    fn tampering_a_binary_byte_breaks_a_per_instruction_fact() {
        let mut cert = CountdownCertificate::produce();
        cert.bytes[12] ^= 0xFF;
        let err = cert
            .recheck()
            .expect_err("a tampered binary must be rejected");
        assert!(
            err.contains("binary-tied fact"),
            "rejection must come from the binary-tie, got: {err}"
        );
    }

    #[test]
    fn tampering_the_program_logic_proof_is_rejected() {
        let mut cert = CountdownCertificate::produce();
        let (prop, _) = loop_capstone_gen();
        cert.program_logic = (prop, step());
        let err = cert
            .recheck()
            .expect_err("a tampered proof must be rejected");
        assert!(
            err.contains("program logic rejected"),
            "rejection must come from the program-logic check, got: {err}"
        );
    }
}
