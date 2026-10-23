import Collatz.MCycle110Certs29

/-!
# Certificates of the listed shapes of `data110`, chunks 116..119
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_116 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_116 = true := by
  decide +kernel

theorem certs110_117 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_117 = true := by
  decide +kernel

theorem certs110_118 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_118 = true := by
  decide +kernel

theorem certs110_119 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_119 = true := by
  decide +kernel

end Collatz
