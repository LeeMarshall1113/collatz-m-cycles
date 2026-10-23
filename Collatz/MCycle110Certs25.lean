import Collatz.MCycle110Certs24

/-!
# Certificates of the listed shapes of `data110`, chunks 96..99
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_96 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_96 = true := by
  decide +kernel

theorem certs110_97 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_97 = true := by
  decide +kernel

theorem certs110_98 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_98 = true := by
  decide +kernel

theorem certs110_99 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_99 = true := by
  decide +kernel

end Collatz
