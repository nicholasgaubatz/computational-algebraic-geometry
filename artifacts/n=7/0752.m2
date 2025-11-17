                                                                                                                                                                              2   2   2   2   2   2   2   2   2   2    2
HashTable{AOTideal => ideal (y y  - y y   + y y  , y y  - y y  + y y , y y  - y y   + y y  , y y  - y y  + y y , y y  - y y  - y y , y y  - y y  - y y , y y  - y y  - y y , y , y , y , y , y , y , y , y , y , y  , y  )}
                              6 7    6 11    7 11   5 7    5 9    7 9   3 4    3 11    4 11   2 4    2 9    4 9   1 4    1 7    4 7   1 3    1 6    3 6   1 2    1 5    2 5   1   2   3   4   5   6   7   8   9   10   11
                                2    2    2   2   2               2   2   2                     2         2         2
          AOTinIdeal => ideal (y  , y  , y , y , y , y y , y y , y , y , y , y y , y y , y y , y , y y , y , y y , y , y y y , y y y , y y y )
                                11   10   9   8   7   6 7   5 7   6   5   4   3 4   2 4   1 4   3   1 3   2   1 2   1   5 6 9   2 3 9   2 3 5
          graph => {set {0, 3}, set {3, 4}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 4}, set {4, 6}, set {2, 5}, set {5, 6}}
                                  2       3       4      5      6
          hSeries => 1 + 11T + 48T  + 106T  + 125T  + 75T  + 18T
          hyperplanes => {a - d, d - e, d - f, d - g, a - e, a - f, a - g, b - e, e - g, c - f, f - g}
          numVariables => 11
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_11]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_6*y_7-y_6*y_11+y_7*y_11, y_5*y_7-y_5*y_9+y_7*y_9, y_3*y_4-y_3*y_11+y_4*y_11, y_2*y_4-y_2*y_9+y_4*y_9, y_1*y_4-y_1*y_7-y_4*y_7, y_1*y_3-y_1*y_6-y_3*y_6, y_1*y_2-y_1*y_5-y_2*y_5, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}},{{y_11^2, y_10^2, y_9^2, y_8^2, y_7^2, y_6*y_7, y_5*y_7, y_6^2, y_5^2, y_4^2, y_3*y_4, y_2*y_4, y_1*y_4, y_3^2, y_1*y_3, y_2^2, y_1*y_2, y_1^2, y_5*y_6*y_9, y_2*y_3*y_9, y_2*y_3*y_5}})
G = graph {set {0, 3}, set {3, 4}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 4}, set {4, 6}, set {2, 5}, set {5, 6}}
