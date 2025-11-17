                                                                                                                                                                                                                                      2   2   2   2   2   2   2   2   2   2    2    2    2
HashTable{AOTideal => ideal (y  y   - y  y   + y  y  , y y   - y y   + y  y  , y y  - y y   + y y  , y y  - y y   - y y  , y y  - y y   - y y  , y y  - y y   - y y  , y y  - y y  - y y , y y  - y y   + y y  , y y  - y y  - y y , y , y , y , y , y , y , y , y , y , y  , y  , y  , y  )}
                              11 12    11 13    12 13   9 10    9 13    10 13   7 8    7 13    8 13   6 8    6 12    8 12   5 8    5 10    8 10   6 7    6 11    7 11   5 7    5 9    7 9   3 4    3 13    4 13   1 2    1 4    2 4   1   2   3   4   5   6   7   8   9   10   11   12   13
                                2    2            2    2           2   2                     2               2   2   2         2   2         2
          AOTinIdeal => ideal (y  , y  , y  y  , y  , y  , y y  , y , y , y y , y y , y y , y , y y , y y , y , y , y , y y , y , y , y y , y , y y y  , y y y )
                                13   12   11 12   11   10   9 10   9   8   7 8   6 8   5 8   7   6 7   5 7   6   5   4   3 4   3   2   1 2   1   5 6 10   5 6 9
          graph => {set {0, 3}, set {3, 6}, set {0, 5}, set {0, 6}, set {1, 4}, set {2, 4}, set {4, 5}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}, set {5, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 13T + 69T  + 191T  + 290T  + 228T  + 72T
          hyperplanes => {a - d, d - g, a - f, a - g, b - e, c - e, e - f, e - g, b - f, b - g, c - f, c - g, f - g}
          numVariables => 13
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_13]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_11*y_12-y_11*y_13+y_12*y_13, y_9*y_10-y_9*y_13+y_10*y_13, y_7*y_8-y_7*y_13+y_8*y_13, y_6*y_8-y_6*y_12-y_8*y_12, y_5*y_8-y_5*y_10-y_8*y_10, y_6*y_7-y_6*y_11-y_7*y_11, y_5*y_7-y_5*y_9-y_7*y_9, y_3*y_4-y_3*y_13+y_4*y_13, y_1*y_2-y_1*y_4-y_2*y_4, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2, y_12^2, y_13^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}},{{y_13^2, y_12^2, y_11*y_12, y_11^2, y_10^2, y_9*y_10, y_9^2, y_8^2, y_7*y_8, y_6*y_8, y_5*y_8, y_7^2, y_6*y_7, y_5*y_7, y_6^2, y_5^2, y_4^2, y_3*y_4, y_3^2, y_2^2, y_1*y_2, y_1^2, y_5*y_6*y_10, y_5*y_6*y_9}})
G = graph {set {0, 3}, set {3, 6}, set {0, 5}, set {0, 6}, set {1, 4}, set {2, 4}, set {4, 5}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}, set {5, 6}}
