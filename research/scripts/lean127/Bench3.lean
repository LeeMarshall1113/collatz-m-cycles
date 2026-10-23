import Collatz.TwoRiseCheck2
set_option Elab.async false
namespace Collatz.TwoRise2
open Collatz.TwoRise

#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T small10 start {t}"
theorem small10 : rangeOK2 97951 97965 20 196006 10 10 (powLo 196006 64 ((2 ^ (196006 + 1) + 1) / 3) 10 1) = true := by
  decide +kernel
#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T small10 end {t}"

#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T q1 start {t}"
theorem q1 : rangeOK2 97951 97965 20 196006 116 1 (powLo 196006 64 ((2 ^ (196006 + 1) + 1) / 3) 116 1) = true := by
  decide +kernel
#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T q1 end {t}"

#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T q16 start {t}"
theorem q16 : rangeOK2 97951 97965 20 196006 116 16 (powLo 196006 64 ((2 ^ (196006 + 1) + 1) / 3) 116 1) = true := by
  decide +kernel
#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T q16 end {t}"

#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T q64 start {t}"
theorem q64 : rangeOK2 97951 97965 20 196006 164 64 (powLo 196006 64 ((2 ^ (196006 + 1) + 1) / 3) 164 1) = true := by
  decide +kernel
#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T q64 end {t}"

#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T qmid16 start {t}"
theorem qmid16 : rangeOK2 97951 97965 20 196006 48816 16 (powLo 196006 64 ((2 ^ (196006 + 1) + 1) / 3) 48816 1) = true := by
  decide +kernel
#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T qmid16 end {t}"

#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T qlate16 start {t}"
theorem qlate16 : rangeOK2 97951 97965 20 196006 97015 16 (powLo 196006 64 ((2 ^ (196006 + 1) + 1) / 3) 97015 1) = true := by
  decide +kernel
#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T qlate16 end {t}"

#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T q256 start {t}"
theorem q256 : rangeOK2 97951 97965 20 196006 420 256 (powLo 196006 64 ((2 ^ (196006 + 1) + 1) / 3) 420 1) = true := by
  decide +kernel
#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T q256 end {t}"

#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T p152_16 start {t}"
theorem p152_16 : rangeOK2 151960 151978 24 304032 116 16 (powLo 304032 64 ((2 ^ (304032 + 1) + 1) / 3) 116 1) = true := by
  decide +kernel
#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T p152_16 end {t}"

#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T p247_16 start {t}"
theorem p247_16 : rangeOK2 247533 247549 22 495174 116 16 (powLo 495174 64 ((2 ^ (495174 + 1) + 1) / 3) 116 1) = true := by
  decide +kernel
#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T p247_16 end {t}"

#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T p647_8 start {t}"
theorem p647_8 : rangeOK2 647476 647493 23 1295062 108 8 (powLo 1295062 64 ((2 ^ (1295062 + 1) + 1) / 3) 108 1) = true := by
  decide +kernel
#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T p647_8 end {t}"

#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T p647_32 start {t}"
theorem p647_32 : rangeOK2 647476 647493 23 1295062 140 32 (powLo 1295062 64 ((2 ^ (1295062 + 1) + 1) / 3) 140 1) = true := by
  decide +kernel
#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T p647_32 end {t}"

end Collatz.TwoRise2
