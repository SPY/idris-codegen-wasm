(module
    (import "rts" "print_i32" (func $print_i32 (param i32)))

    (memory $mem 10)

    (; STACK BEGIN ;)
    (global $stack-start (export "stack-start") i32 (i32.const 1024))
    (global $stack-end (export "stack-end") i32 (i32.const 2048))
    (global $stack-base (mut i32) (i32.const 0))
    (global $stack-top (mut i32) (i32.const 0))

    (func $get-stack-base (export "get-stack-base") (result i32)
        (get_global $stack-base)
    )

    (func $set-stack-base (export "set-stack-base") (param $val i32)
        (set_global $stack-base (get_local $val))
    )

    (func $show-stack-base (export "show-stack-base")
        (call $print_i32 (get_global $stack-base))
    )
    (; STACK END ;)

    (; HEAP BEGIN ;)
    (global $heap-start (mut i32) (i32.const 0))
    (global $heap-end (mut i32) (i32.const 0))
    (global $heap-next (mut i32) (i32.const 0))

    (func $alligned (param $size i32) (result i32)
        (get_local $size)
    )

    (func $alloc (param $size i32) (result i32)
        (local $aligned-size i32)
        (local $addr i32)
        (set_local $aligned-size (call $alligned (get_local $size)))
        (if (i32.lt_u (i32.add (get_global $heap-next) (get_local $aligned-size)) (get_global $heap-end))
            (then
                (set_local $addr (get_global $heap-next))
                (set_global $heap-next (i32.add (get_global $heap-next) (get_local $aligned-size)))
                (get_local $addr)
            )
            (else
                (call $run-gc)
                (call $alloc (get_local $size))
            )
        )
    )

    (func $run-gc
        (nop)
    )
    (; HEAP END ;)
)
