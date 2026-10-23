import Collatz.MCycle108Certs29

/-!
# Certificates of the listed shapes of `data108`, chunks 116..119
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs108_116 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_116 = true := by
  decide +kernel

theorem certs108_117 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_117 = true := by
  decide +kernel

theorem certs108_118 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_118 = true := by
  decide +kernel

theorem certs108_119 : certsOK3 108 20 grid108 grid3_107 data108.certs shapes108_119 = true := by
  decide +kernel

end Collatz
