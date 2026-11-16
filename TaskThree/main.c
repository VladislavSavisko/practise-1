/*
 * Практична робота №3. Програма для анкетування.
 *
 * Можливості:
 *  - анкета: ім'я, прізвище, вік, статус студента (булева змінна);
 *  - зберігання даних у текстовому файлі users.csv;
 *  - при старті файл читається, а якщо його немає - створюється новий;
 *  - виведення кількох анкет, зокрема з фільтром за ім'ям;
 *  - авторизація за логіном і паролем, ролі "адміністратор" і "користувач";
 *  - пароль не зберігається: у файл пишеться сіль і хеш SHA-256.
 *
 * Компіляція: gcc main.c -o survey
 */
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#ifndef _WIN32
#include <termios.h>
#include <unistd.h>
#endif

#define DATA_FILE "users.csv"
#define CSV_HEADER "login,salt,password_hash,role,first_name,last_name,age,is_student"
#define MAX_USERS 1000
#define STR_LEN 64
#define SALT_LEN 16      /* 8 випадкових байтів у шістнадцятковому записі */
#define HASH_LEN 64      /* SHA-256 у шістнадцятковому записі */
#define HASH_ROUNDS 10000

typedef enum { ROLE_USER = 0, ROLE_ADMIN = 1 } Role;

typedef struct {
    char login[STR_LEN];
    char salt[SALT_LEN + 1];
    char hash[HASH_LEN + 1];
    Role role;
    char first_name[STR_LEN];
    char last_name[STR_LEN];
    int age;
    bool is_student;
} User;

static User users[MAX_USERS];
static int user_count = 0;

/* ------------------------------ SHA-256 ------------------------------ */

static const uint32_t K[64] = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2};

static uint32_t rotr(uint32_t x, int n) { return (x >> n) | (x << (32 - n)); }

static void sha256_block(uint32_t state[8], const uint8_t block[64])
{
    uint32_t w[64];
    for (int i = 0; i < 16; i++)
        w[i] = ((uint32_t)block[i * 4] << 24) | ((uint32_t)block[i * 4 + 1] << 16) |
               ((uint32_t)block[i * 4 + 2] << 8) | (uint32_t)block[i * 4 + 3];
    for (int i = 16; i < 64; i++) {
        uint32_t s0 = rotr(w[i - 15], 7) ^ rotr(w[i - 15], 18) ^ (w[i - 15] >> 3);
        uint32_t s1 = rotr(w[i - 2], 17) ^ rotr(w[i - 2], 19) ^ (w[i - 2] >> 10);
        w[i] = w[i - 16] + s0 + w[i - 7] + s1;
    }
    uint32_t a = state[0], b = state[1], c = state[2], d = state[3];
    uint32_t e = state[4], f = state[5], g = state[6], h = state[7];
    for (int i = 0; i < 64; i++) {
        uint32_t s1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25);
        uint32_t ch = (e & f) ^ (~e & g);
        uint32_t t1 = h + s1 + ch + K[i] + w[i];
        uint32_t s0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22);
        uint32_t maj = (a & b) ^ (a & c) ^ (b & c);
        uint32_t t2 = s0 + maj;
        h = g; g = f; f = e; e = d + t1;
        d = c; c = b; b = a; a = t1 + t2;
    }
    state[0] += a; state[1] += b; state[2] += c; state[3] += d;
    state[4] += e; state[5] += f; state[6] += g; state[7] += h;
}

/* Обчислює SHA-256 від data довжиною len байтів, результат - 32 байти. */
static void sha256(const uint8_t *data, size_t len, uint8_t out[32])
{
    uint32_t state[8] = {0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
                         0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19};
    uint8_t block[64];
    size_t full = len / 64;
    for (size_t i = 0; i < full; i++)
        sha256_block(state, data + i * 64);

    size_t rest = len % 64;
    memset(block, 0, sizeof block);
    memcpy(block, data + full * 64, rest);
    block[rest] = 0x80;
    if (rest >= 56) {
        sha256_block(state, block);
        memset(block, 0, sizeof block);
    }
    uint64_t bits = (uint64_t)len * 8;
    for (int i = 0; i < 8; i++)
        block[63 - i] = (uint8_t)(bits >> (8 * i));
    sha256_block(state, block);

    for (int i = 0; i < 8; i++) {
        out[i * 4] = (uint8_t)(state[i] >> 24);
        out[i * 4 + 1] = (uint8_t)(state[i] >> 16);
        out[i * 4 + 2] = (uint8_t)(state[i] >> 8);
        out[i * 4 + 3] = (uint8_t)state[i];
    }
}

static void to_hex(const uint8_t *bytes, size_t n, char *out)
{
    for (size_t i = 0; i < n; i++)
        sprintf(out + i * 2, "%02x", bytes[i]);
}

/* Хеш пароля: SHA-256 від "сіль:пароль", повторений HASH_ROUNDS разів. */
static void hash_password(const char *password, const char *salt, char out[HASH_LEN + 1])
{
    char buf[SALT_LEN + STR_LEN + 2];
    uint8_t digest[32];
    int n = snprintf(buf, sizeof buf, "%s:%s", salt, password);
    sha256((const uint8_t *)buf, (size_t)n, digest);
    for (int i = 0; i < HASH_ROUNDS; i++)
        sha256(digest, sizeof digest, digest);
    to_hex(digest, sizeof digest, out);
}

/* Випадкова сіль, щоб однакові паролі мали різні хеші. */
static void make_salt(char out[SALT_LEN + 1])
{
    uint8_t bytes[SALT_LEN / 2];
    FILE *f = fopen("/dev/urandom", "rb");
    bool ok = f != NULL && fread(bytes, 1, sizeof bytes, f) == sizeof bytes;
    if (f != NULL)
        fclose(f);
    if (!ok) {
        srand((unsigned)time(NULL) ^ (unsigned)clock());
        for (size_t i = 0; i < sizeof bytes; i++)
            bytes[i] = (uint8_t)(rand() & 0xff);
    }
    to_hex(bytes, sizeof bytes, out);
}

/* --------------------------- Введення даних --------------------------- */

/* Читає рядок; якщо ввід закінчився - завершує програму. */
static void read_raw(const char *prompt, char *buf, size_t size)
{
    printf("%s", prompt);
    fflush(stdout);
    if (fgets(buf, (int)size, stdin) == NULL) {
        printf("\nВвід завершено. До побачення!\n");
        exit(0);
    }
    size_t len = strlen(buf);
    if (len > 0 && buf[len - 1] == '\n') {
        buf[len - 1] = '\0';
    } else {
        int c; /* рядок задовгий - відкидаємо залишок */
        while ((c = getchar()) != '\n' && c != EOF) {
        }
    }
    len = strlen(buf);
    if (len > 0 && buf[len - 1] == '\r')
        buf[len - 1] = '\0';
}

/* Читає непорожній рядок без ком (кома - роздільник у CSV). */
static void read_text(const char *prompt, char *buf, size_t size)
{
    for (;;) {
        read_raw(prompt, buf, size);
        if (buf[0] == '\0')
            printf("  Поле не може бути порожнім.\n");
        else if (strchr(buf, ',') != NULL)
            printf("  Кома в цьому полі не дозволена.\n");
        else
            return;
    }
}

static int read_int(const char *prompt, int min, int max)
{
    char buf[32];
    for (;;) {
        read_raw(prompt, buf, sizeof buf);
        char *end;
        long value = strtol(buf, &end, 10);
        if (buf[0] != '\0' && *end == '\0' && value >= min && value <= max)
            return (int)value;
        printf("  Введіть ціле число від %d до %d.\n", min, max);
    }
}

/* Відповідь "так/ні": приймає т, н, y, n, 1, 0. */
static bool read_bool(const char *prompt)
{
    char buf[32];
    for (;;) {
        read_raw(prompt, buf, sizeof buf);
        if (buf[0] == 'y' || buf[0] == 'Y' || buf[0] == '1' ||
            strncmp(buf, "т", 2) == 0 || strncmp(buf, "Т", 2) == 0)
            return true;
        if (buf[0] == 'n' || buf[0] == 'N' || buf[0] == '0' ||
            strncmp(buf, "н", 2) == 0 || strncmp(buf, "Н", 2) == 0)
            return false;
        printf("  Дайте відповідь: т (так) або н (ні).\n");
    }
}

/* Читає пароль, не показуючи його на екрані. */
static void read_password(const char *prompt, char *buf, size_t size)
{
#ifndef _WIN32
    struct termios old_settings, hidden;
    bool is_terminal = isatty(STDIN_FILENO) && tcgetattr(STDIN_FILENO, &old_settings) == 0;
    if (is_terminal) {
        hidden = old_settings;
        hidden.c_lflag &= ~(tcflag_t)ECHO;
        tcsetattr(STDIN_FILENO, TCSANOW, &hidden);
    }
    read_raw(prompt, buf, size);
    if (is_terminal) {
        tcsetattr(STDIN_FILENO, TCSANOW, &old_settings);
        printf("\n");
    }
#else
    read_raw(prompt, buf, size);
#endif
}

/* ------------------------- Робота з файлом ------------------------- */

/* Записує всіх користувачів у файл. Повертає true, якщо вдалося. */
static bool save_users(void)
{
    FILE *f = fopen(DATA_FILE, "w");
    if (f == NULL) {
        printf("Помилка: не вдалося записати файл %s.\n", DATA_FILE);
        return false;
    }
    fprintf(f, "%s\n", CSV_HEADER);
    for (int i = 0; i < user_count; i++) {
        const User *u = &users[i];
        fprintf(f, "%s,%s,%s,%s,%s,%s,%d,%s\n", u->login, u->salt, u->hash,
                u->role == ROLE_ADMIN ? "admin" : "user", u->first_name, u->last_name,
                u->age, u->is_student ? "true" : "false");
    }
    return fclose(f) == 0;
}

/* Читає файл. Повертає false, якщо файлу немає. */
static bool load_users(void)
{
    FILE *f = fopen(DATA_FILE, "r");
    if (f == NULL)
        return false;

    char line[512];
    int line_number = 0;
    user_count = 0;
    while (fgets(line, sizeof line, f) != NULL) {
        line_number++;
        line[strcspn(line, "\r\n")] = '\0';
        if (line_number == 1 || line[0] == '\0')
            continue; /* заголовок або порожній рядок */
        if (user_count >= MAX_USERS) {
            printf("Увага: у файлі забагато записів, зайві пропущено.\n");
            break;
        }
        User u;
        char role[16], student[16];
        int fields = sscanf(line, "%63[^,],%16[^,],%64[^,],%15[^,],%63[^,],%63[^,],%d,%15s",
                            u.login, u.salt, u.hash, role, u.first_name, u.last_name,
                            &u.age, student);
        if (fields != 8) {
            printf("Увага: рядок %d файлу пошкоджений і пропущений.\n", line_number);
            continue;
        }
        u.role = strcmp(role, "admin") == 0 ? ROLE_ADMIN : ROLE_USER;
        u.is_student = strcmp(student, "true") == 0;
        users[user_count++] = u;
    }
    fclose(f);
    return true;
}

/* --------------------------- Виведення даних --------------------------- */

static const char *role_name(Role role)
{
    return role == ROLE_ADMIN ? "адміністратор" : "користувач";
}

/* Друкує рядок і доповнює пробілами до ширини width (у символах, а не байтах). */
static void print_padded(const char *text, int width)
{
    int chars = 0;
    for (const char *p = text; *p != '\0'; p++)
        if (((unsigned char)*p & 0xC0) != 0x80)
            chars++;
    printf("%s", text);
    for (int i = chars; i < width; i++)
        putchar(' ');
}

static void print_user(const User *u)
{
    printf("  Логін:    %s\n", u->login);
    printf("  Статус:   %s\n", role_name(u->role));
    printf("  Ім'я:     %s\n", u->first_name);
    printf("  Прізвище: %s\n", u->last_name);
    printf("  Вік:      %d\n", u->age);
    printf("  Студент:  %s\n", u->is_student ? "так" : "ні");
}

/* Виводить таблицю анкет. Якщо name_filter не NULL - лише з таким іменем. */
static void print_table(const char *name_filter)
{
    int shown = 0;
    print_padded("№", 4);
    print_padded("Логін", 14);
    print_padded("Ім'я", 14);
    print_padded("Прізвище", 16);
    print_padded("Вік", 5);
    print_padded("Студент", 9);
    printf("Статус\n");
    printf("--------------------------------------------------------------------------\n");
    for (int i = 0; i < user_count; i++) {
        const User *u = &users[i];
        if (name_filter != NULL && strcmp(u->first_name, name_filter) != 0)
            continue;
        char number[16], age[16];
        snprintf(number, sizeof number, "%d", ++shown);
        snprintf(age, sizeof age, "%d", u->age);
        print_padded(number, 4);
        print_padded(u->login, 14);
        print_padded(u->first_name, 14);
        print_padded(u->last_name, 16);
        print_padded(age, 5);
        print_padded(u->is_student ? "так" : "ні", 9);
        printf("%s\n", role_name(u->role));
    }
    if (shown == 0)
        printf("(анкет не знайдено)\n");
    else
        printf("Усього анкет: %d\n", shown);
}

/* ------------------------- Облікові записи ------------------------- */

static User *find_user(const char *login)
{
    for (int i = 0; i < user_count; i++)
        if (strcmp(users[i].login, login) == 0)
            return &users[i];
    return NULL;
}

static int count_admins(void)
{
    int count = 0;
    for (int i = 0; i < user_count; i++)
        if (users[i].role == ROLE_ADMIN)
            count++;
    return count;
}

/* Анкета: ім'я, прізвище, вік і чи є студентом. */
static void fill_questionnaire(User *u)
{
    read_text("Ім'я: ", u->first_name, sizeof u->first_name);
    read_text("Прізвище: ", u->last_name, sizeof u->last_name);
    u->age = read_int("Вік: ", 1, 120);
    u->is_student = read_bool("Чи є студентом? (т/н): ");
}

/* Створює обліковий запис із заданою роллю. Повертає запис або NULL. */
static User *create_account(Role role)
{
    if (user_count >= MAX_USERS) {
        printf("Неможливо додати: досягнуто максимуму записів.\n");
        return NULL;
    }
    User u;
    memset(&u, 0, sizeof u);
    u.role = role;

    for (;;) {
        read_text("Логін: ", u.login, sizeof u.login);
        if (find_user(u.login) == NULL)
            break;
        printf("  Такий логін уже зайнятий.\n");
    }

    char password[STR_LEN], repeat[STR_LEN];
    for (;;) {
        read_password("Пароль (не менше 4 символів): ", password, sizeof password);
        if (strlen(password) < 4) {
            printf("  Пароль закороткий.\n");
            continue;
        }
        read_password("Повторіть пароль: ", repeat, sizeof repeat);
        if (strcmp(password, repeat) == 0)
            break;
        printf("  Паролі не збігаються.\n");
    }
    make_salt(u.salt);
    hash_password(password, u.salt, u.hash);
    memset(password, 0, sizeof password);
    memset(repeat, 0, sizeof repeat);

    fill_questionnaire(&u);

    users[user_count++] = u;
    if (!save_users()) {
        user_count--;
        return NULL;
    }
    printf("\nДані збережено у файл %s:\n", DATA_FILE);
    print_user(&users[user_count - 1]);
    return &users[user_count - 1];
}

/* Вхід за логіном і паролем. Повертає користувача або NULL. */
static User *log_in(void)
{
    char login[STR_LEN], password[STR_LEN], hash[HASH_LEN + 1];
    read_raw("Логін: ", login, sizeof login);
    read_password("Пароль: ", password, sizeof password);

    User *u = find_user(login);
    bool ok = false;
    if (u != NULL) {
        hash_password(password, u->salt, hash);
        ok = strcmp(hash, u->hash) == 0;
    }
    memset(password, 0, sizeof password);
    if (!ok) {
        printf("Неправильний логін або пароль.\n");
        return NULL;
    }
    printf("Вітаємо, %s %s! Ваш статус: %s.\n", u->first_name, u->last_name, role_name(u->role));
    return u;
}

/* ------------------------------- Меню ------------------------------- */

static void user_menu(const User *current)
{
    for (;;) {
        printf("\n--- Меню користувача (%s) ---\n", current->login);
        printf("1. Переглянути свої дані\n");
        printf("0. Вийти з облікового запису\n");
        int choice = read_int("Ваш вибір: ", 0, 1);
        if (choice == 0)
            return;
        printf("\nВаші дані:\n");
        print_user(current);
    }
}

static void admin_menu(const char *current_login)
{
    for (;;) {
        printf("\n--- Меню адміністратора (%s) ---\n", current_login);
        printf("1. Створити нового користувача\n");
        printf("2. Переглянути всі анкети\n");
        printf("3. Знайти анкети за ім'ям\n");
        printf("4. Переглянути свої дані\n");
        printf("0. Вийти з облікового запису\n");
        int choice = read_int("Ваш вибір: ", 0, 4);
        printf("\n");
        if (choice == 0) {
            return;
        } else if (choice == 1) {
            printf("Статус нового запису: 1 - користувач, 2 - адміністратор\n");
            Role role = read_int("Ваш вибір: ", 1, 2) == 2 ? ROLE_ADMIN : ROLE_USER;
            create_account(role);
        } else if (choice == 2) {
            print_table(NULL);
        } else if (choice == 3) {
            char name[STR_LEN];
            read_text("Ім'я для пошуку: ", name, sizeof name);
            print_table(name);
        } else {
            /* масив users міг змінитися, тому шукаємо запис заново */
            const User *me = find_user(current_login);
            if (me != NULL) {
                printf("Ваші дані:\n");
                print_user(me);
            }
        }
    }
}

int main(void)
{
    printf("=== Програма анкетування ===\n");

    if (load_users()) {
        printf("Файл %s прочитано, записів: %d.\n", DATA_FILE, user_count);
    } else {
        printf("Файл %s не знайдено. Створюю новий файл.\n", DATA_FILE);
        if (!save_users())
            return 1;
    }

    if (count_admins() == 0) {
        printf("\nУ системі ще немає адміністратора. Створіть його обліковий запис.\n");
        if (create_account(ROLE_ADMIN) == NULL)
            return 1;
    }

    for (;;) {
        printf("\n--- Головне меню ---\n");
        printf("1. Вхід\n");
        printf("2. Реєстрація\n");
        printf("0. Вихід із програми\n");
        int choice = read_int("Ваш вибір: ", 0, 2);
        printf("\n");
        if (choice == 0) {
            printf("До побачення!\n");
            return 0;
        } else if (choice == 1) {
            User *u = log_in();
            if (u == NULL)
                continue;
            if (u->role == ROLE_ADMIN) {
                char login[STR_LEN];
                strcpy(login, u->login);
                admin_menu(login);
            } else {
                user_menu(u);
            }
        } else {
            printf("Реєстрація нового користувача. Заповніть анкету.\n");
            create_account(ROLE_USER);
        }
    }
}
