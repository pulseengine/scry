# fixture-15-stack-alloca

FEAT-021 **slice-1** soundness regression (DD-016 guardrail 1).

`$allocish` has a **constant** prologue frame (16) **and** a later **dynamic**
decrement of the `__stack_pointer` (`global.get 0; local.get 0; i32.sub` — an
`alloca` of a runtime size). Its true peak frame is `16 + param`, not statically
bounded, so the detector must report **Unknown** — never the constant 16.

This fixture pins a soundness bug caught by **clean-room review** of the initial
slice-1 detector: that version checked the single-constant-frame case *before*
the dynamic one, so it returned `Bytes(16)` (an **under-count**). The detector
now counts *every* SP decrement — constant and dynamic — and any dynamic or
extra decrement forces `Unknown`.

## Source

```wat
(func $allocish (export "allocish") (param i32) (result i32)
  global.get 0  i32.const 16   i32.sub  global.set 0   ;; constant frame 16
  global.get 0  local.get 0    i32.sub  global.set 0   ;; dynamic: SP -= param
  i32.const 0)
```

Native oracle: `feat021_const_frame_plus_dynamic_is_unknown` asserts the
function frame and the module bound are both `Unknown`.
