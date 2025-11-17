                                                                                                                                                                                                                              2   2   2   2   2   2   2   2   2   2    2    2    2
HashTable{AOTideal => ideal (y  y   - y  y   - y  y  , y y  - y y   - y y  , y y  - y y   + y y  , y y  - y y  + y y , y y  - y y   + y y  , y y  - y y  + y y , y y  - y y  - y y , y y  - y y  - y y , y y  - y y  - y y , y , y , y , y , y , y , y , y , y , y  , y  , y  , y  )}
                              11 12    11 13    12 13   8 9    8 10    9 10   6 7    6 12    7 12   5 7    5 9    7 9   3 4    3 12    4 12   2 4    2 9    4 9   1 4    1 7    4 7   1 3    1 6    3 6   1 2    1 5    2 5   1   2   3   4   5   6   7   8   9   10   11   12   13
                                2    2            2    2    2         2   2               2   2   2                     2         2         2
          AOTinIdeal => ideal (y  , y  , y  y  , y  , y  , y , y y , y , y , y y , y y , y , y , y , y y , y y , y y , y , y y , y , y y , y , y y y , y y y , y y y , y y y y  , y y y y  )
                                13   12   11 12   11   10   9   8 9   8   7   6 7   5 7   6   5   4   3 4   2 4   1 4   3   1 3   2   1 2   1   5 6 9   2 3 9   2 3 5   5 6 8 10   2 3 8 10
          graph => {set {0, 3}, set {3, 4}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 4}, set {4, 6}, set {1, 6}, set {2, 5}, set {5, 6}, set {2, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 13T + 69T  + 191T  + 290T  + 228T  + 72T
          hyperplanes => {a - d, d - e, d - f, d - g, a - e, a - f, a - g, b - e, e - g, b - g, c - f, f - g, c - g}
          numVariables => 13
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_4"


R = QQ[y_1..y_13]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_11*y_12-y_11*y_13-y_12*y_13, y_8*y_9-y_8*y_10-y_9*y_10, y_6*y_7-y_6*y_12+y_7*y_12, y_5*y_7-y_5*y_9+y_7*y_9, y_3*y_4-y_3*y_12+y_4*y_12, y_2*y_4-y_2*y_9+y_4*y_9, y_1*y_4-y_1*y_7-y_4*y_7, y_1*y_3-y_1*y_6-y_3*y_6, y_1*y_2-y_1*y_5-y_2*y_5, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2, y_12^2, y_13^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-4}, {-4}},{{y_13^2, y_12^2, y_11*y_12, y_11^2, y_10^2, y_9^2, y_8*y_9, y_8^2, y_7^2, y_6*y_7, y_5*y_7, y_6^2, y_5^2, y_4^2, y_3*y_4, y_2*y_4, y_1*y_4, y_3^2, y_1*y_3, y_2^2, y_1*y_2, y_1^2, y_5*y_6*y_9, y_2*y_3*y_9, y_2*y_3*y_5, y_5*y_6*y_8*y_10, y_2*y_3*y_8*y_10}})
G = graph {set {0, 3}, set {3, 4}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 4}, set {4, 6}, set {1, 6}, set {2, 5}, set {5, 6}, set {2, 6}}
