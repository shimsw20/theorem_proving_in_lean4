린4로 하는 정리 증명
-----------------------

이 메뉴얼은 [mdBook](https://github.com/rust-lang/mdBook)으로 생성되었습니다. 우리는 현재 다음 부가 기능을 위해 [fork](https://github.com/leanprover/mdBook)를 사용합니다.

* 다른 언어 [#1339](https://github.com/rust-lang/mdBook/pull/1339)에서 선을 숨기는 것의 지원을 추가하기.
*  `mdbook test`에서 `rustdoc --test`을 호출하는 것을 `./test`으로 대체함.

이 메뉴얼을 생성하려면 fork를 다음을 거쳐 설치해야합니다.
```bash
cargo install --git https://github.com/leanprover/mdBook mdbook
```
루트 폴더에서 [`mdbook watch`](https://rust-lang.github.io/mdBook/cli/watch.html)을 사용합니다.
```bash
mdbook watch을 열고 # 여러분의 기본 브라우저에서 `out/`에서 출력을 여세요.
```

모든  `lean`의 코드 블록을 테스트하려면 `mdbook test`을 실행하세요.

## 작동시키는 법

```
./deploy.sh
```
