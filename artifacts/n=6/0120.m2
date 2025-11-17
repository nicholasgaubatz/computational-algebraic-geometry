                                                                                                              2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  + y y , y y  - y y  + y y , y y  - y y  - y y , y y  - y y  - y y , y , y , y , y , y , y , y , y )}
                              4 5    4 8    5 8   2 3    2 8    3 8   1 3    1 5    3 5   1 2    1 4    2 4   1   2   3   4   5   6   7   8
                                2   2   2   2         2   2               2         2
          AOTinIdeal => ideal (y , y , y , y , y y , y , y , y y , y y , y , y y , y )
                                8   7   6   5   4 5   4   3   2 3   1 3   2   1 2   1
          graph => {set {0, 2}, set {2, 4}, set {2, 5}, set {0, 4}, set {0, 5}, set {1, 3}, set {1, 5}, set {4, 5}}
                                 2      3      4     5
          hSeries => 1 + 8T + 24T  + 34T  + 23T  + 6T
          hyperplanes => {a - c, c - e, c - f, a - e, a - f, b - d, b - f, e - f}
          numVariables => 8
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_8]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_4*y_5-y_4*y_8+y_5*y_8, y_2*y_3-y_2*y_8+y_3*y_8, y_1*y_3-y_1*y_5-y_3*y_5, y_1*y_2-y_1*y_4-y_2*y_4, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_8^2, y_7^2, y_6^2, y_5^2, y_4*y_5, y_4^2, y_3^2, y_2*y_3, y_1*y_3, y_2^2, y_1*y_2, y_1^2}})
G = graph {set {0, 2}, set {2, 4}, set {2, 5}, set {0, 4}, set {0, 5}, set {1, 3}, set {1, 5}, set {4, 5}}
