pub mod core;
pub mod opt;
pub mod rcanary;
pub mod safedrop;
pub mod senryx;
pub mod unsafety_isolation;
pub mod utils;

pub trait Analysis {
    /// Return the name of the analysis.
    fn name(&self) -> &'static str;

    /// Execute the analysis.
    fn run(&mut self);

    /// Reset the analysis result.
    fn reset(&mut self);
}
