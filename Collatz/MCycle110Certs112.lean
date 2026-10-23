import Collatz.MCycle110Certs111

/-!
# Certificates of the listed shapes of `data110`, chunks 444..447
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_444 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_444 = true := by
  decide +kernel

theorem certs110_445 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_445 = true := by
  decide +kernel

theorem certs110_446 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_446 = true := by
  decide +kernel

theorem certs110_447 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_447 = true := by
  decide +kernel

end Collatz
