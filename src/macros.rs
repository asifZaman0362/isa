pub fn convert_case(lexeme: &str) -> String {
    let mut str = String::from(lexeme.as_bytes()[0] as char).to_ascii_uppercase();
    str.push_str(&lexeme[1..]);
    str
}

#[macro_export]
macro_rules! define_mnemonics {
    ( $( $name:ident ),* ) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub enum MnemonicT {
            $( $name ),*
        }

        impl MnemonicT {
            pub fn try_from_str(s: &str) -> Option<Self> {
                match $crate::macros::convert_case(s).as_str() {
                    $( stringify!($name) => Some(MnemonicT::$name), )*
                    _ => None
                }
            }

            pub fn as_str(&self) -> &'static str {
                match self {
                    $( MnemonicT::$name => stringify!($name), )*
                }
            }

            pub fn all() -> &'static [&'static str] {
                &[
                    $( stringify!($name) ),*
                ]
            }
        }
    };
}

#[macro_export]
macro_rules! enum_with_names {
    ($name:ident {
        $($variant:ident $( ($type:ty) )*),*
    }) => {
        #[derive(Debug, Clone, PartialEq)]
        pub enum $name {
            $( $variant $(($type))? ),*
        }

        impl $name {
            pub const fn to_str(&self) -> &'static str {
                paste! {
                    match self {
                        $( $name::$variant $(([<_ $type:lower>]))? => stringify!($variant) ),*
                    }
                }
            }
        }
    }
}

#[macro_export]
macro_rules! discriminate {
    ( $name:ident ) => {
        paste! {
            const [<$name:upper _T>]: TokenKind = TokenKind::$name;
            pub const [<$name:upper>] : &'static str = &[<$name:upper _T>].to_str();
        }
    };
    ( $name:ident, $value:expr ) => {
        paste! {
            const [<$name:upper _T>]: &'static TokenKind = &TokenKind::$name($value);
            pub const [<$name:upper>] : &'static str = &[<$name:upper _T>].to_str();
        }
    };
}
