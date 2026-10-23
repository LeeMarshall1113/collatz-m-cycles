import Collatz.MCycle110Certs7

/-!
# Certificates of the listed shapes of `data110`, chunks 28..31
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_28 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_28 = true := by
  decide +kernel

theorem certs110_29 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_29 = true := by
  decide +kernel

theorem certs110_30 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_30 = true := by
  decide +kernel

theorem certs110_31 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_31 = true := by
  decide +kernel

end Collatz
