import Collatz.MCycle110Certs9

/-!
# Certificates of the listed shapes of `data110`, chunks 36..39
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_36 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_36 = true := by
  decide +kernel

theorem certs110_37 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_37 = true := by
  decide +kernel

theorem certs110_38 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_38 = true := by
  decide +kernel

theorem certs110_39 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_39 = true := by
  decide +kernel

end Collatz
