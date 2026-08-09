/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import Mathlib

/-!
# Mathlib-only statement audit

Root module for the `Audit` Lake library. The individual challenge and solution
modules are intentionally not imported here: each challenge is a standalone
Mathlib-only statement surface, and each corresponding solution imports the
AbsorptionCutoff development explicitly.

Keeping this root module free of challenge imports also lets project-wide tools
such as `checkdecls` import every configured library without introducing the
seven intentional challenge `sorry`s into the default library build.
-/
