pub trait Documentise {
    fn document(&self) -> String;
}

pub mod html;
