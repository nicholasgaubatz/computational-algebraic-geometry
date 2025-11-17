                                                                                          2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  - y y , y y  - y y  - y y , y y  - y y  - y y , y , y , y , y , y , y , y , y )}
                              3 4    3 7    4 7   2 4    2 6    4 6   1 4    1 5    4 5   1   2   3   4   5   6   7   8
                                2   2   2   2   2                     2   2   2
          AOTinIdeal => ideal (y , y , y , y , y , y y , y y , y y , y , y , y , y y y , y y y , y y y )
                                8   7   6   5   4   3 4   2 4   1 4   3   2   1   2 3 6   1 3 5   1 2 5
          graph => {set {0, 4}, set {1, 4}, set {2, 4}, set {4, 5}, set {0, 5}, set {1, 5}, set {2, 5}, set {3, 5}}
                                 2      3      4     5
          hSeries => 1 + 8T + 25T  + 38T  + 28T  + 8T
          hyperplanes => {a - e, b - e, c - e, e - f, a - f, b - f, c - f, d - f}
          numVariables => 8
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_8]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_3*y_4-y_3*y_7-y_4*y_7, y_2*y_4-y_2*y_6-y_4*y_6, y_1*y_4-y_1*y_5-y_4*y_5, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}},{{y_8^2, y_7^2, y_6^2, y_5^2, y_4^2, y_3*y_4, y_2*y_4, y_1*y_4, y_3^2, y_2^2, y_1^2, y_2*y_3*y_6, y_1*y_3*y_5, y_1*y_2*y_5}})
G = graph {set {0, 4}, set {1, 4}, set {2, 4}, set {4, 5}, set {0, 5}, set {1, 5}, set {2, 5}, set {3, 5}}
