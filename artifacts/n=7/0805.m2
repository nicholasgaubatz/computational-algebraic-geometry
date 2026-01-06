                                                                                                                                                                                                                                                           2   2   2   2   2   2   2   2   2   2    2    2
HashTable{AOTideal => ideal (y  y   - y  y   + y  y  , y y  - y y   - y y  , y y  - y y   + y y  , y y  - y y  + y y , y y  - y y  - y y , y y y  - y y y   - y y y   + y y y  , y y y  - y y y   + y y y   + y y y  , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y , y , y  , y  , y  )}
                              10 11    10 12    11 12   8 9    8 11    9 11   5 6    5 12    6 12   4 6    4 9    6 9   1 3    1 5    3 5   4 5 8    4 5 10    4 8 10    5 8 10   2 3 7    2 3 12    2 7 12    3 7 12   1 2 6    1 2 7    1 6 7    2 6 7   1   2   3   4   5   6   7   8   9   10   11   12
                                2    2            2    2         2   2   2               2   2   2         2   2
          AOTinIdeal => ideal (y  , y  , y  y  , y  , y , y y , y , y , y , y y , y y , y , y , y , y y , y , y , y y y , y y y , y y y , y y y , y y y y , y y y y )
                                12   11   10 11   10   9   8 9   8   7   6   5 6   4 6   5   4   3   1 3   2   1   4 5 9   4 5 8   2 3 7   1 2 6   1 2 5 7   1 2 4 7
          graph => {set {0, 3}, set {1, 3}, set {3, 5}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 6}, set {2, 4}, set {4, 6}, set {2, 5}, set {2, 6}, set {5, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 12T + 61T  + 167T  + 258T  + 211T  + 70T
          hyperplanes => {a - d, b - d, d - f, a - e, a - f, a - g, b - g, c - e, e - g, c - f, c - g, f - g}
          numVariables => 12
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_4"


R = QQ[y_1..y_12]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_10*y_11-y_10*y_12+y_11*y_12, y_8*y_9-y_8*y_11-y_9*y_11, y_5*y_6-y_5*y_12+y_6*y_12, y_4*y_6-y_4*y_9+y_6*y_9, y_1*y_3-y_1*y_5-y_3*y_5, y_4*y_5*y_8-y_4*y_5*y_10-y_4*y_8*y_10+y_5*y_8*y_10, y_2*y_3*y_7-y_2*y_3*y_12+y_2*y_7*y_12+y_3*y_7*y_12, y_1*y_2*y_6-y_1*y_2*y_7-y_1*y_6*y_7+y_2*y_6*y_7, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2, y_12^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-4}, {-4}},{{y_12^2, y_11^2, y_10*y_11, y_10^2, y_9^2, y_8*y_9, y_8^2, y_7^2, y_6^2, y_5*y_6, y_4*y_6, y_5^2, y_4^2, y_3^2, y_1*y_3, y_2^2, y_1^2, y_4*y_5*y_9, y_4*y_5*y_8, y_2*y_3*y_7, y_1*y_2*y_6, y_1*y_2*y_5*y_7, y_1*y_2*y_4*y_7}})
G = graph {set {0, 3}, set {1, 3}, set {3, 5}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 6}, set {2, 4}, set {4, 6}, set {2, 5}, set {2, 6}, set {5, 6}}
