/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.MeanMap.Basic
import AbsorptionCutoff.MeanMap.Derivative
import AbsorptionCutoff.MeanMap.Dynamics

/-!
# The squared-radius mean map and its fixed points

Compatibility import preserving the public `AbsorptionCutoff.MeanMap` API. The implementation
is split into `Basic`, `Derivative`, and `Dynamics` so downstream modules can depend on
the smallest coherent layer they need.
-/
