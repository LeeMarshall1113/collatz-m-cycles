import Collatz.MCycle110Certs36

/-!
# Certificates of the listed shapes of `data110`, chunks 144..147
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_144 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_144 = true := by
  decide +kernel

theorem certs110_145 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_145 = true := by
  decide +kernel

theorem certs110_146 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_146 = true := by
  decide +kernel

theorem certs110_147 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_147 = true := by
  decide +kernel

end Collatz
