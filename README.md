# Слайдинг при обобщённой гладкости

- [Постановка задачи](<исследовательская задача.md>) описывает цель исследования и исходные статьи.
- [Исходные статьи](orig/), [переводы](ru/) и [аннотации](annot/) собраны отдельно. Обозначения вынесены в [заметку по статье Borodich и соавторов](annot/Borodich_et_al_2025_notation_ru.md).
- [Черновик LaTeX](formalize/l0_l1.tex) объединяет постановку, оценки и ограничения методов.
- [Промежуточные результаты](intermediate_results/) включают [рекурсивную схему](intermediate_results/path_a_replacement.md), [неускоренную схему](intermediate_results/path_b_plain.md), [ускоренную схему](intermediate_results/path_c_accelerated.md) и [заметку о динамических весах](intermediate_results/multilevel_sliding_research.md).
- [Архив](trash/) содержит ранние планы исследования.

## Формализация в Lean

Точка входа находится в [LeanLab.lean](LeanLab/LeanLab.lean). Сборка запускается командой `lake build` из каталога LeanLab.

| Тема | Модули |
| --- | --- |
| Обобщённая гладкость и расписание рекурсии | [SymmetricSmoothness](LeanLab/LeanLab/SymmetricSmoothness.lean), [SlidingGeneralizedSmoothness](LeanLab/LeanLab/SlidingGeneralizedSmoothness.lean), [PathASchedule](LeanLab/LeanLab/PathASchedule.lean) |
| Двухуровневая схема и перезапуски | [TwoLevelSliding](LeanLab/LeanLab/TwoLevelSliding.lean), [TwoLevelSearch](LeanLab/LeanLab/TwoLevelSearch.lean) |
| Неускоренный слайдинг и подбор шага | [PlainSliding](LeanLab/LeanLab/PlainSliding.lean), [AdaptivePlainSliding](LeanLab/LeanLab/AdaptivePlainSliding.lean), [PlainSlidingStepSearch](LeanLab/LeanLab/PlainSlidingStepSearch.lean) |
| Рекурсия варианта А на локализованном множестве | [LocalizedRecursiveSliding](LeanLab/LeanLab/LocalizedRecursiveSliding.lean) |
| Ускоренная и многоуровневая схемы | [AdaptiveAcceleratedSliding](LeanLab/LeanLab/AdaptiveAcceleratedSliding.lean), [MultilevelSliding](LeanLab/LeanLab/MultilevelSliding.lean) |

## GitHub configuration for LeanLab

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

