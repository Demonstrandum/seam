pub trait Documentise {
    fn document(&self) -> String;
}

pub mod xml;
pub mod html;
