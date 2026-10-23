import Collatz.MCycle110Certs30

/-!
# Certificates of the listed shapes of `data110`, chunks 120..123
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_120 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_120 = true := by
  decide +kernel

theorem certs110_121 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_121 = true := by
  decide +kernel

theorem certs110_122 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_122 = true := by
  decide +kernel

theorem certs110_123 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_123 = true := by
  decide +kernel

end Collatz
