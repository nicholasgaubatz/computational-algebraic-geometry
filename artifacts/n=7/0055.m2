                                                                                                                                      2   2   2   2   2   2   2   2   2   2    2
HashTable{AOTideal => ideal (y y  - y y   - y y  , y y  - y y   - y y  , y y  - y y  - y y , y y  - y y  - y y , y y  - y y  - y y , y , y , y , y , y , y , y , y , y , y  , y  )         }
                              5 6    5 11    6 11   4 6    4 10    6 10   3 6    3 9    6 9   2 6    2 8    6 8   1 6    1 7    6 7   1   2   3   4   5   6   7   8   9   10   11
                                2    2    2   2   2   2                                 2   2   2   2   2
          AOTinIdeal => ideal (y  , y  , y , y , y , y , y y , y y , y y , y y , y y , y , y , y , y , y , y y y  , y y y , y y y , y y y , y y y , y y y , y y y , y y y , y y y , y y y )
                                11   10   9   8   7   6   5 6   4 6   3 6   2 6   1 6   5   4   3   2   1   4 5 10   3 5 9   3 4 9   2 5 8   2 4 8   2 3 8   1 5 7   1 4 7   1 3 7   1 2 7
          graph => {set {0, 5}, set {1, 5}, set {2, 5}, set {3, 5}, set {4, 5}, set {5, 6}, set {0, 6}, set {1, 6}, set {2, 6}, set {3, 6}, set {4, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 11T + 50T  + 120T  + 160T  + 112T  + 32T
          hyperplanes => {a - f, b - f, c - f, d - f, e - f, f - g, a - g, b - g, c - g, d - g, e - g}
          numVariables => 11
          WLPfull => "A does not have WLP at A_4"
          WLPin => "A does not have WLP at A_4"


R = QQ[y_1..y_11]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_5*y_6-y_5*y_11-y_6*y_11, y_4*y_6-y_4*y_10-y_6*y_10, y_3*y_6-y_3*y_9-y_6*y_9, y_2*y_6-y_2*y_8-y_6*y_8, y_1*y_6-y_1*y_7-y_6*y_7, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}},{{y_11^2, y_10^2, y_9^2, y_8^2, y_7^2, y_6^2, y_5*y_6, y_4*y_6, y_3*y_6, y_2*y_6, y_1*y_6, y_5^2, y_4^2, y_3^2, y_2^2, y_1^2, y_4*y_5*y_10, y_3*y_5*y_9, y_3*y_4*y_9, y_2*y_5*y_8, y_2*y_4*y_8, y_2*y_3*y_8, y_1*y_5*y_7, y_1*y_4*y_7, y_1*y_3*y_7, y_1*y_2*y_7}})
G = graph {set {0, 5}, set {1, 5}, set {2, 5}, set {3, 5}, set {4, 5}, set {5, 6}, set {0, 6}, set {1, 6}, set {2, 6}, set {3, 6}, set {4, 6}}
