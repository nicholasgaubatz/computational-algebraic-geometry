                                                                                                                                                                                                                                                                        2   2   2   2   2   2   2   2   2   2    2    2    2
HashTable{AOTideal => ideal (y  y   - y  y   + y  y  , y y   - y y   - y  y  , y y  - y y   + y y  , y y  - y y   + y y  , y y  - y y   + y y  , y y  - y y  - y y , y y  - y y  - y y , y y  - y y  - y y , y y y y  - y y y y   + y y y y   - y y y y   - y y y y  , y , y , y , y , y , y , y , y , y , y  , y  , y  , y  )}
                              11 12    11 13    12 13   9 10    9 12    10 12   7 8    7 13    8 13   5 6    5 10    6 10   3 4    3 13    4 13   2 4    2 8    4 8   1 4    1 6    4 6   2 3    2 7    3 7   1 3 5 9    1 3 5 11    1 3 9 11    1 5 9 11    3 5 9 11   1   2   3   4   5   6   7   8   9   10   11   12   13
                                2    2            2    2           2   2         2   2         2   2                     2         2   2
          AOTinIdeal => ideal (y  , y  , y  y  , y  , y  , y y  , y , y , y y , y , y , y y , y , y , y y , y y , y y , y , y y , y , y , y y y , y y y , y y y y  , y y y y , y y y y , y y y y y  , y y y y y )
                                13   12   11 12   11   10   9 10   9   8   7 8   7   6   5 6   5   4   3 4   2 4   1 4   3   2 3   2   1   1 3 6   1 2 6   1 3 5 10   1 3 5 9   1 2 5 8   1 2 5 7 10   1 2 5 7 9
          graph => {set {0, 3}, set {1, 3}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 6}, set {1, 5}, set {1, 6}, set {2, 4}, set {4, 6}, set {2, 5}, set {2, 6}, set {5, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 13T + 70T  + 200T  + 319T  + 267T  + 90T
          hyperplanes => {a - d, b - d, d - f, d - g, a - e, a - g, b - f, b - g, c - e, e - g, c - f, c - g, f - g}
          numVariables => 13
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_4"


R = QQ[y_1..y_13]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-4}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_11*y_12-y_11*y_13+y_12*y_13, y_9*y_10-y_9*y_12-y_10*y_12, y_7*y_8-y_7*y_13+y_8*y_13, y_5*y_6-y_5*y_10+y_6*y_10, y_3*y_4-y_3*y_13+y_4*y_13, y_2*y_4-y_2*y_8-y_4*y_8, y_1*y_4-y_1*y_6-y_4*y_6, y_2*y_3-y_2*y_7-y_3*y_7, y_1*y_3*y_5*y_9-y_1*y_3*y_5*y_11+y_1*y_3*y_9*y_11-y_1*y_5*y_9*y_11-y_3*y_5*y_9*y_11, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2, y_12^2, y_13^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-4}, {-4}, {-4}, {-5}, {-5}},{{y_13^2, y_12^2, y_11*y_12, y_11^2, y_10^2, y_9*y_10, y_9^2, y_8^2, y_7*y_8, y_7^2, y_6^2, y_5*y_6, y_5^2, y_4^2, y_3*y_4, y_2*y_4, y_1*y_4, y_3^2, y_2*y_3, y_2^2, y_1^2, y_1*y_3*y_6, y_1*y_2*y_6, y_1*y_3*y_5*y_10, y_1*y_3*y_5*y_9, y_1*y_2*y_5*y_8, y_1*y_2*y_5*y_7*y_10, y_1*y_2*y_5*y_7*y_9}})
G = graph {set {0, 3}, set {1, 3}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 6}, set {1, 5}, set {1, 6}, set {2, 4}, set {4, 6}, set {2, 5}, set {2, 6}, set {5, 6}}
