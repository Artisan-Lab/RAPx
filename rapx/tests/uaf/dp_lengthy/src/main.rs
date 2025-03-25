use std::{
    alloc::{alloc_zeroed, dealloc, Layout},
    num::NonZeroUsize,
};

fn main() {
    let layout = Layout::new::<NonZeroUsize>();
    let ptr = {
        let mut param = {
            let array: [*mut u8; 2] = [
                {
                    struct Struct(*mut u8, String);

                    let tuple_struct = Struct(
                        { unsafe { alloc_zeroed(layout) } },
                        String::from("Hello, world!"),
                    );
                    tuple_struct.0
                },
                { &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize as *mut u8 },
            ];
            let [first, ..] = array;
            first
        };
        loop {
            param = {
                enum Enum {
                    Place(*mut u8),
                    Other(String),
                }

                let tuple_enum = Enum::Place({
                    enum Enum {
                        Place(*mut u8),
                        Other(String),
                    }

                    let tuple_enum = Enum::Place({
                        struct Struct {
                            place: *mut u8,
                            other: String,
                        };

                        let struct_struct = Struct {
                            place: { param },
                            other: String::from("Hello, world!"),
                        };
                        struct_struct.place
                    });
                    if let Enum::Place(param) = tuple_enum {
                        {
                            enum Enum {
                                Place(*mut u8),
                                Other(String),
                            }

                            let tuple_enum = Enum::Place({
                                let mut boxed_array = Box::new([{ param }, {
                                    &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize
                                        as *mut u8
                                }]);
                                let slice: &mut [*mut u8] = &mut boxed_array[..];
                                std::mem::replace(&mut slice[0], {
                                    &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize
                                        as *mut u8
                                })
                            });
                            if let Enum::Place(param) = tuple_enum {
                                {
                                    struct Struct {
                                        place: *mut u8,
                                        other: String,
                                    };

                                    let base = Struct {
                                        place: { param },
                                        other: String::from("Hello, world!"),
                                    };
                                    let struct_struct = Struct {
                                        other: String::from("Hello, world!"),
                                        ..base
                                    };
                                    struct_struct.place
                                }
                            } else {
                                {
                                    &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize
                                        as *mut u8
                                }
                            }
                        }
                    } else {
                        {
                            &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize as *mut u8
                        }
                    }
                });
                if let Enum::Place(param) = tuple_enum {
                    {
                        fn call(param: *mut u8) -> *mut u8 {
                            {
                                struct Struct(*mut u8, String);

                                let tuple_struct = Struct(
                                    {
                                        struct Struct {
                                            place: *mut u8,
                                            other: String,
                                        };

                                        let base = Struct {
                                            place: { param },
                                            other: String::from("Hello, world!"),
                                        };
                                        let struct_struct = Struct {
                                            other: String::from("Hello, world!"),
                                            ..base
                                        };
                                        struct_struct.place
                                    },
                                    String::from("Hello, world!"),
                                );
                                tuple_struct.0
                            }
                        }
                        call({
                            struct Struct {
                                place: *mut u8,
                                other: String,
                            };

                            let struct_struct = Struct {
                                place: {
                                    let array: [*mut u8; 2] = [{ param }, {
                                        &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize
                                            as *mut u8
                                    }];
                                    let [first, ..] = array;
                                    first
                                },
                                other: String::from("Hello, world!"),
                            };
                            struct_struct.place
                        })
                    }
                } else {
                    {
                        &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize as *mut u8
                    }
                }
            };
            if true {
                break {
                    if let Some(param) = Some({
                        match Some({
                            struct Struct {
                                place: *mut u8,
                                other: String,
                            };

                            let struct_struct = Struct {
                                place: { param },
                                other: String::from("Hello, world!"),
                            };
                            struct_struct.place
                        }) {
                            Some(param) => {
                                let mut param = {
                                    fn call(param: *mut u8) -> *mut u8 {
                                        {
                                            param
                                        }
                                    }
                                    call({ param })
                                };
                                loop {
                                    param = {
                                        let param = {
                                            fn call(param: *mut u8) -> *mut u8 {
                                                {
                                                    param
                                                }
                                            }
                                            call({ param })
                                        };
                                        if let if_let = param {
                                            {
                                                let slice: &mut [*mut u8] = &mut [{ if_let }, {
                                                    &mut NonZeroUsize::new(1).unwrap()
                                                        as *mut NonZeroUsize
                                                        as *mut u8
                                                }][..];
                                                std::mem::replace(&mut slice[0], {
                                                    &mut NonZeroUsize::new(1).unwrap()
                                                        as *mut NonZeroUsize
                                                        as *mut u8
                                                })
                                            }
                                        } else {
                                            {
                                                &mut NonZeroUsize::new(1).unwrap()
                                                    as *mut NonZeroUsize
                                                    as *mut u8
                                            }
                                        }
                                    };
                                    if let if_let = param {
                                        break {
                                            enum Enum {
                                                Place { place: *mut u8, other: String },
                                                Other(String),
                                            }

                                            let struct_enum = Enum::Place {
                                                place: {
                                                    fn call(param: *mut u8) -> *mut u8 {
                                                        {
                                                            param
                                                        }
                                                    }
                                                    call({ if_let })
                                                },
                                                other: String::from("Hello, world!"),
                                            };
                                            match struct_enum {
                                                Enum::Place {
                                                    place: param,
                                                    other: _,
                                                } => {
                                                    struct Struct {
                                                        place: *mut u8,
                                                        other: String,
                                                    };

                                                    let struct_struct = Struct {
                                                        place: {
                                                            fn call(param: *mut u8) -> *mut u8 {
                                                                {
                                                                    param
                                                                }
                                                            }
                                                            call({ param })
                                                        },
                                                        other: String::from("Hello, world!"),
                                                    };
                                                    struct_struct.place
                                                }
                                                Enum::Other(_) => {
                                                    &mut NonZeroUsize::new(1).unwrap()
                                                        as *mut NonZeroUsize
                                                        as *mut u8
                                                }
                                            }
                                        };
                                    } else {
                                        break {
                                            &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize
                                                as *mut u8
                                        };
                                    }
                                }
                            }
                            None => {
                                &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize as *mut u8
                            }
                        }
                    }) {
                        {
                            let param = {
                                struct Struct {
                                    place: *mut u8,
                                    other: String,
                                };

                                let struct_struct = Struct {
                                    place: {
                                        let mut boxed_array = Box::new([{ param }, {
                                            &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize
                                                as *mut u8
                                        }]);
                                        let slice: &mut [*mut u8] = &mut boxed_array[..];
                                        std::mem::replace(&mut slice[0], {
                                            &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize
                                                as *mut u8
                                        })
                                    },
                                    other: String::from("Hello, world!"),
                                };
                                struct_struct.place
                            };
                            if true {
                                {
                                    let mut param = {
                                        struct Struct {
                                            place: *mut u8,
                                            other: String,
                                        };

                                        let base = Struct {
                                            place: { param },
                                            other: String::from("Hello, world!"),
                                        };
                                        let struct_struct = Struct {
                                            other: String::from("Hello, world!"),
                                            ..base
                                        };
                                        struct_struct.place
                                    };
                                    loop {
                                        param = {
                                            match Some({
                                                let mut boxed_array = Box::new([{ param }, {
                                                    &mut NonZeroUsize::new(1).unwrap()
                                                        as *mut NonZeroUsize
                                                        as *mut u8
                                                }]);
                                                let slice: &mut [*mut u8] = &mut boxed_array[..];
                                                std::mem::replace(&mut slice[0], {
                                                    &mut NonZeroUsize::new(1).unwrap()
                                                        as *mut NonZeroUsize
                                                        as *mut u8
                                                })
                                            }) {
                                                Some(param) => {
                                                    enum Enum {
                                                        Place(*mut u8),
                                                        Other(String),
                                                    }

                                                    let tuple_enum = Enum::Place({ param });
                                                    if let Enum::Place(param) = tuple_enum {
                                                        {
                                                            let tuple: (*mut u8, String) = (
                                                                { param },
                                                                String::from("Hello, world!"),
                                                            );
                                                            tuple.0
                                                        }
                                                    } else {
                                                        {
                                                            &mut NonZeroUsize::new(1).unwrap()
                                                                as *mut NonZeroUsize
                                                                as *mut u8
                                                        }
                                                    }
                                                }
                                                None => &mut NonZeroUsize::new(1).unwrap()
                                                    as *mut NonZeroUsize
                                                    as *mut u8,
                                            }
                                        };
                                        if true {
                                            break {
                                                struct Struct(*mut u8, String);

                                                let tuple_struct = Struct(
                                                    {
                                                        struct Struct {
                                                            place: *mut u8,
                                                            other: String,
                                                        };

                                                        let struct_struct = Struct {
                                                            place: { param },
                                                            other: String::from("Hello, world!"),
                                                        };
                                                        struct_struct.place
                                                    },
                                                    String::from("Hello, world!"),
                                                );
                                                tuple_struct.0
                                            };
                                        } else {
                                            break {
                                                struct Struct {
                                                    place: *mut u8,
                                                    other: String,
                                                };

                                                let struct_struct = Struct {
                                                    place: { param },
                                                    other: String::from("Hello, world!"),
                                                };
                                                struct_struct.place
                                            };
                                        }
                                    }
                                }
                            } else {
                                {
                                    fn call(param: *mut u8) -> *mut u8 {
                                        {
                                            let mut param = {
                                                let mut param = {
                                                    fn call(param: *mut u8) -> *mut u8 {
                                                        {
                                                            param
                                                        }
                                                    }
                                                    call({ param })
                                                };
                                                let mut i = 0;
                                                while i < 32 {
                                                    param = {
                                                        let mut param = { param };
                                                        loop {
                                                            param = {
                                                                fn call(param: *mut u8) -> *mut u8 {
                                                                    {
                                                                        param
                                                                    }
                                                                }
                                                                call({ param })
                                                            };
                                                            if let if_let = param {
                                                                break {
                                                                    struct Struct(*mut u8, String);

                                                                    let tuple_struct = Struct(
                                                                        { if_let },
                                                                        String::from(
                                                                            "Hello, world!",
                                                                        ),
                                                                    );
                                                                    tuple_struct.0
                                                                };
                                                            } else {
                                                                break {
                                                                    &mut NonZeroUsize::new(1)
                                                                        .unwrap()
                                                                        as *mut NonZeroUsize
                                                                        as *mut u8
                                                                };
                                                            }
                                                        }
                                                    };
                                                    i = i + 1;
                                                }
                                                param
                                            };
                                            let mut i = 0;
                                            while i < 32 {
                                                param = {
                                                    let param = {
                                                        enum Enum {
                                                            Place(*mut u8),
                                                            Other(String),
                                                        }

                                                        let tuple_enum = Enum::Place({
                                                            fn call(param: *mut u8) -> *mut u8 {
                                                                {
                                                                    param
                                                                }
                                                            }
                                                            call({ param })
                                                        });
                                                        if let Enum::Place(param) = tuple_enum {
                                                            {
                                                                let param = { param };
                                                                if true {
                                                                    {
                                                                        enum Enum {
                                                                            Place(*mut u8),
                                                                            Other(String),
                                                                        }

                                                                        let tuple_enum =
                                                                            Enum::Place({ param });
                                                                        match tuple_enum {
                                                                        Enum::Place(param) => {
                                                                            struct Struct {
                                                                                place: *mut u8,
                                                                                other: String
                                                                            };

                                                                            let base = Struct {
                                                                                place: {
                                                                                    param
                                                                                },
                                                                                other: String::from("Hello, world!")
                                                                            };
                                                                            let struct_struct = Struct { other: String::from("Hello, world!"), ..base};
                                                                            struct_struct.place
                                                                        },
                                                                        Enum::Other(_) => {
                                                                            &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize as *mut u8
                                                                        },
                                                                    }
                                                                    }
                                                                } else {
                                                                    {
                                                                        let tuple: (
                                                                            *mut u8,
                                                                            String,
                                                                        ) = (
                                                                            { param },
                                                                            String::from(
                                                                                "Hello, world!",
                                                                            ),
                                                                        );
                                                                        tuple.0
                                                                    }
                                                                }
                                                            }
                                                        } else {
                                                            {
                                                                &mut NonZeroUsize::new(1).unwrap()
                                                                    as *mut NonZeroUsize
                                                                    as *mut u8
                                                            }
                                                        }
                                                    };
                                                    if true {
                                                        {
                                                            struct Struct {
                                                                place: *mut u8,
                                                                other: String,
                                                            };

                                                            let struct_struct = Struct {
                                                                place: {
                                                                    match { param } {
                                                                        param => {
                                                                            if let Some(param) =
                                                                                Some({ param })
                                                                            {
                                                                                {
                                                                                    enum Enum {
                                                                                        Place{ place: *mut u8, other: String },
                                                                                        Other(String),
                                                                                    }

                                                                                    let struct_enum = Enum::Place{ place: {
                                                                                        param
                                                                                    }, other: String::from("Hello, world!") };
                                                                                    if let Enum::Place{ place: param, other: _ } = struct_enum {
                                                                                        {
                                                                                            let slice: &mut [*mut u8] = &mut [{
                                                                                                param
                                                                                            }, {
                                                                                                &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize as *mut u8
                                                                                            }][..];
                                                                                            std::mem::replace(&mut slice[0], {
                                                                                                &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize as *mut u8
                                                                                            })
                                                                                        }
                                                                                    } else {
                                                                                        {
                                                                                            &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize as *mut u8
                                                                                        }
                                                                                    }
                                                                                }
                                                                            } else {
                                                                                {
                                                                                    &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize as *mut u8
                                                                                }
                                                                            }
                                                                        }
                                                                        _ => {
                                                                            &mut NonZeroUsize::new(
                                                                                1,
                                                                            )
                                                                            .unwrap()
                                                                                as *mut NonZeroUsize
                                                                                as *mut u8
                                                                        }
                                                                    }
                                                                },
                                                                other: String::from(
                                                                    "Hello, world!",
                                                                ),
                                                            };
                                                            struct_struct.place
                                                        }
                                                    } else {
                                                        {
                                                            let mut param = {
                                                                let mut param = { param };
                                                                loop {
                                                                    param = {
                                                                        let array: [*mut u8; 2] = [
                                                                            { param },
                                                                            {
                                                                                &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize as *mut u8
                                                                            },
                                                                        ];
                                                                        let [first, ..] = array;
                                                                        first
                                                                    };
                                                                    if true {
                                                                        break {
                                                                            let param = { param };
                                                                            if true {
                                                                                {
                                                                                    enum Enum {
                                                                                        Place(
                                                                                            *mut u8,
                                                                                        ),
                                                                                        Other(
                                                                                            String,
                                                                                        ),
                                                                                    }

                                                                                    let tuple_enum =
                                                                                        Enum::Place(
                                                                                            {
                                                                                                param
                                                                                            },
                                                                                        );
                                                                                    match tuple_enum {
                                                                                        Enum::Place(param) => {
                                                                                            struct Struct {
                                                                                                place: *mut u8,
                                                                                                other: String
                                                                                            };

                                                                                            let base = Struct {
                                                                                                place: {
                                                                                                    param
                                                                                                },
                                                                                                other: String::from("Hello, world!")
                                                                                            };
                                                                                            let struct_struct = Struct { other: String::from("Hello, world!"), ..base};
                                                                                            struct_struct.place
                                                                                        },
                                                                                        Enum::Other(_) => {
                                                                                            &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize as *mut u8
                                                                                        },
                                                                                    }
                                                                                }
                                                                            } else {
                                                                                {
                                                                                    let tuple: (*mut u8, String) = ({
                                                                                                                        param
                                                                                                                    }, String::from("Hello, world!"));
                                                                                    tuple.0
                                                                                }
                                                                            }
                                                                        };
                                                                    } else {
                                                                        break {
                                                                            if let Some(param) =
                                                                                Some({ param })
                                                                            {
                                                                                {
                                                                                    enum Enum {
                                                                                        Place{ place: *mut u8, other: String },
                                                                                        Other(String),
                                                                                    }

                                                                                    let struct_enum = Enum::Place{ place: {
                                                                                        param
                                                                                    }, other: String::from("Hello, world!") };
                                                                                    if let Enum::Place{ place: param, other: _ } = struct_enum {
                                                                                        {
                                                                                            let slice: &mut [*mut u8] = &mut [{
                                                                                                param
                                                                                            }, {
                                                                                                &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize as *mut u8
                                                                                            }][..];
                                                                                            std::mem::replace(&mut slice[0], {
                                                                                                &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize as *mut u8
                                                                                            })
                                                                                        }
                                                                                    } else {
                                                                                        {
                                                                                            &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize as *mut u8
                                                                                        }
                                                                                    }
                                                                                }
                                                                            } else {
                                                                                {
                                                                                    &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize as *mut u8
                                                                                }
                                                                            }
                                                                        };
                                                                    }
                                                                }
                                                            };
                                                            loop {
                                                                param = {
                                                                    enum Enum {
                                                                        Place(*mut u8),
                                                                        Other(String),
                                                                    }

                                                                    let tuple_enum = Enum::Place({
                                                                        struct Struct {
                                                                            place: *mut u8,
                                                                            other: String,
                                                                        };

                                                                        let base = Struct {
                                                                            place: { param },
                                                                            other: String::from(
                                                                                "Hello, world!",
                                                                            ),
                                                                        };
                                                                        let struct_struct =
                                                                            Struct {
                                                                                other: String::from(
                                                                                    "Hello, world!",
                                                                                ),
                                                                                ..base
                                                                            };
                                                                        struct_struct.place
                                                                    });
                                                                    if let Enum::Place(param) =
                                                                        tuple_enum
                                                                    {
                                                                        {
                                                                            if let Some(param) =
                                                                                Some({
                                                                                    let array: [*mut u8; 2] = [{
                                                                                param
                                                                            }, {
                                                                                &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize as *mut u8
                                                                            }];
                                                                                    let [first, ..] =
                                                                                        array;
                                                                                    first
                                                                                })
                                                                            {
                                                                                {
                                                                                    enum Enum {
                                                                                        Place(
                                                                                            *mut u8,
                                                                                        ),
                                                                                        Other(
                                                                                            String,
                                                                                        ),
                                                                                    }

                                                                                    let tuple_enum =
                                                                                        Enum::Place(
                                                                                            {
                                                                                                param
                                                                                            },
                                                                                        );
                                                                                    match tuple_enum {
                                                                                    Enum::Place(param) => {
                                                                                        struct Struct {
                                                                                            place: *mut u8,
                                                                                            other: String
                                                                                        };

                                                                                        let base = Struct {
                                                                                            place: {
                                                                                                param
                                                                                            },
                                                                                            other: String::from("Hello, world!")
                                                                                        };
                                                                                        let struct_struct = Struct { other: String::from("Hello, world!"), ..base};
                                                                                        struct_struct.place
                                                                                    },
                                                                                    Enum::Other(_) => {
                                                                                        &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize as *mut u8
                                                                                    },
                                                                                }
                                                                                }
                                                                            } else {
                                                                                {
                                                                                    &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize as *mut u8
                                                                                }
                                                                            }
                                                                        }
                                                                    } else {
                                                                        {
                                                                            &mut NonZeroUsize::new(
                                                                                1,
                                                                            )
                                                                            .unwrap()
                                                                                as *mut NonZeroUsize
                                                                                as *mut u8
                                                                        }
                                                                    }
                                                                };
                                                                if let if_let = param {
                                                                    break {
                                                                        enum Enum {
                                                                            Place {
                                                                                place: *mut u8,
                                                                                other: String,
                                                                            },
                                                                            Other(String),
                                                                        }

                                                                        let struct_enum =
                                                                            Enum::Place {
                                                                                place: {
                                                                                    enum Enum {
                                                                                        Place(
                                                                                            *mut u8,
                                                                                        ),
                                                                                        Other(
                                                                                            String,
                                                                                        ),
                                                                                    }

                                                                                    let tuple_enum =
                                                                                        Enum::Place(
                                                                                            {
                                                                                                if_let
                                                                                            },
                                                                                        );
                                                                                    if let Enum::Place(param) = tuple_enum { {
                                                                                let tuple: (*mut u8, String) = ({
                                                                                                                    param
                                                                                                                }, String::from("Hello, world!"));
                                                                                tuple.0
                                                                            }
                                                                            } else {
                                                                                {
                                                                                    &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize as *mut u8
                                                                                }
                                                                            }
                                                                                },
                                                                                other: String::from(
                                                                                    "Hello, world!",
                                                                                ),
                                                                            };
                                                                        if let Enum::Place {
                                                                            place: param,
                                                                            other: _,
                                                                        } = struct_enum
                                                                        {
                                                                            {
                                                                                struct Struct {
                                                                                    place: *mut u8,
                                                                                    other: String,
                                                                                };

                                                                                let struct_struct = Struct {
                                                                                    place: {
                                                                                        let tuple: (*mut u8, String) = ({
                                                                                                                            param
                                                                                                                        }, String::from("Hello, world!"));
                                                                                        tuple.0
                                                                                    },
                                                                                    other: String::from("Hello, world!")
                                                                                };
                                                                                struct_struct.place
                                                                            }
                                                                        } else {
                                                                            {
                                                                                &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize as *mut u8
                                                                            }
                                                                        }
                                                                    };
                                                                } else {
                                                                    break {
                                                                        &mut NonZeroUsize::new(1)
                                                                            .unwrap()
                                                                            as *mut NonZeroUsize
                                                                            as *mut u8
                                                                    };
                                                                }
                                                            }
                                                        }
                                                    }
                                                };
                                                i = i + 1;
                                            }
                                            param
                                        }
                                    }
                                    call({
                                        enum Enum {
                                            Place(*mut u8),
                                            Other(String),
                                        }

                                        let tuple_enum = Enum::Place({
                                            let slice: &mut [*mut u8] = &mut [{ param }, {
                                                &mut NonZeroUsize::new(1).unwrap()
                                                    as *mut NonZeroUsize
                                                    as *mut u8
                                            }][..];
                                            std::mem::replace(&mut slice[0], {
                                                &mut NonZeroUsize::new(1).unwrap()
                                                    as *mut NonZeroUsize
                                                    as *mut u8
                                            })
                                        });
                                        if let Enum::Place(param) = tuple_enum {
                                            {
                                                enum Enum {
                                                    Place(*mut u8),
                                                    Other(String),
                                                }

                                                let tuple_enum = Enum::Place({ param });
                                                if let Enum::Place(param) = tuple_enum {
                                                    {
                                                        let tuple: (*mut u8, String) = (
                                                            { param },
                                                            String::from("Hello, world!"),
                                                        );
                                                        tuple.0
                                                    }
                                                } else {
                                                    {
                                                        &mut NonZeroUsize::new(1).unwrap()
                                                            as *mut NonZeroUsize
                                                            as *mut u8
                                                    }
                                                }
                                            }
                                        } else {
                                            {
                                                &mut NonZeroUsize::new(1).unwrap()
                                                    as *mut NonZeroUsize
                                                    as *mut u8
                                            }
                                        }
                                    })
                                }
                            }
                        }
                    } else {
                        {
                            &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize as *mut u8
                        }
                    }
                };
            } else {
                break {
                    fn call(param: *mut u8) -> *mut u8 {
                        {
                            struct Struct(*mut u8, String);

                            let tuple_struct = Struct(
                                {
                                    let array: [*mut u8; 2] = [
                                        {
                                            let array: [*mut u8; 2] = [{ param }, {
                                                &mut NonZeroUsize::new(1).unwrap()
                                                    as *mut NonZeroUsize
                                                    as *mut u8
                                            }];
                                            let [first, ..] = array;
                                            first
                                        },
                                        {
                                            &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize
                                                as *mut u8
                                        },
                                    ];
                                    let [first, ..] = array;
                                    first
                                },
                                String::from("Hello, world!"),
                            );
                            tuple_struct.0
                        }
                    }
                    call({
                        let mut param = {
                            let mut boxed_array = Box::new([{ param }, {
                                &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize as *mut u8
                            }]);
                            let slice: &mut [*mut u8] = &mut boxed_array[..];
                            std::mem::replace(&mut slice[0], {
                                &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize as *mut u8
                            })
                        };
                        loop {
                            param = {
                                let slice: &mut [*mut u8] = &mut [
                                    {
                                        let slice: &mut [*mut u8] = &mut [{ param }, {
                                            &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize
                                                as *mut u8
                                        }][..];
                                        std::mem::replace(&mut slice[0], {
                                            &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize
                                                as *mut u8
                                        })
                                    },
                                    {
                                        &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize
                                            as *mut u8
                                    },
                                ][..];
                                std::mem::replace(&mut slice[0], {
                                    &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize
                                        as *mut u8
                                })
                            };
                            if let if_let = param {
                                break {
                                    enum Enum {
                                        Place { place: *mut u8, other: String },
                                        Other(String),
                                    }

                                    let struct_enum = Enum::Place {
                                        place: {
                                            let mut boxed_array = Box::new([{ if_let }, {
                                                &mut NonZeroUsize::new(1).unwrap()
                                                    as *mut NonZeroUsize
                                                    as *mut u8
                                            }]);
                                            let slice: &mut [*mut u8] = &mut boxed_array[..];
                                            std::mem::replace(&mut slice[0], {
                                                &mut NonZeroUsize::new(1).unwrap()
                                                    as *mut NonZeroUsize
                                                    as *mut u8
                                            })
                                        },
                                        other: String::from("Hello, world!"),
                                    };
                                    match struct_enum {
                                        Enum::Place {
                                            place: param,
                                            other: _,
                                        } => {
                                            enum Enum {
                                                Place { place: *mut u8, other: String },
                                                Other(String),
                                            }

                                            let struct_enum = Enum::Place {
                                                place: {
                                                    let tuple: (*mut u8, String) =
                                                        ({ param }, String::from("Hello, world!"));
                                                    tuple.0
                                                },
                                                other: String::from("Hello, world!"),
                                            };
                                            if let Enum::Place {
                                                place: param,
                                                other: _,
                                            } = struct_enum
                                            {
                                                {
                                                    match {
                                                        fn call(param: *mut u8) -> *mut u8 {
                                                            {
                                                                param
                                                            }
                                                        }
                                                        call({ param })
                                                    } {
                                                        param => {
                                                            fn call(param: *mut u8) -> *mut u8 {
                                                                {
                                                                    param
                                                                }
                                                            }
                                                            call({ param })
                                                        }
                                                        _ => &mut NonZeroUsize::new(1).unwrap()
                                                            as *mut NonZeroUsize
                                                            as *mut u8,
                                                    }
                                                }
                                            } else {
                                                {
                                                    &mut NonZeroUsize::new(1).unwrap()
                                                        as *mut NonZeroUsize
                                                        as *mut u8
                                                }
                                            }
                                        }
                                        Enum::Other(_) => &mut NonZeroUsize::new(1).unwrap()
                                            as *mut NonZeroUsize
                                            as *mut u8,
                                    }
                                };
                            } else {
                                break {
                                    &mut NonZeroUsize::new(1).unwrap() as *mut NonZeroUsize
                                        as *mut u8
                                };
                            }
                        }
                    })
                };
            }
        }
    }; // SOURCE

    unsafe {
        let _ = (*(ptr as *mut NonZeroUsize)).get(); // BAD SINK
        dealloc(ptr, layout);
    }
}
