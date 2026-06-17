# fixture-14-stack-dynamic

FEAT-021 **slice-1** corpus — dynamic frame → **Unknown** (DD-016 guardrail 1).

`$dyn` subtracts a *runtime* value (the param — an `alloca`-style
variable-size allocation) from the `__stack_pointer` rather than a constant:
`global.get 0; local.get 0; i32.sub; global.set 0`. The frame is not
statically known, so scry reports **UNKNOWN** for the function and the module
— a sound admission of ignorance, **never** a zero under-count.

## Source

```wat
(func $dyn (export "dyn") (param i32) (result i32)
  global.get 0  local.get 0  i32.sub  global.set 0   ;; SP -= param (dynamic)
  i32.const 0)
```

Native oracle: `feat021_stack_dynamic_frame_is_unknown` asserts the function's
frame and the module bound are both `Unknown`. (The detector recognises only
the `global.get SP; i32.const F; i32.sub` constant-frame prologue; any other
write to SP — including a variable subtract or a second decrement — yields
`Unknown`.)
