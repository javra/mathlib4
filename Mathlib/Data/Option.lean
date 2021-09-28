/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jakob von Raumer
-/
namespace Option

@[inline] def getOrElse {α : Type u} : Option α → α → α
| some x, _ => x
| none  , x => x

end Option
