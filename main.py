#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Teracoin (TRC) — blockchain própria, inspirada no Bitcoin.

Uso:
    python main.py                      # roda o nó (minera + web + P2P)
    python main.py rodar --sem-minerar  # nó que só valida e repassa
    python main.py carteira             # mostra o endereço da sua carteira
    python main.py enviar ENDERECO 1.5  # envia TRC (precisa do nó rodando)

Variáveis de ambiente úteis:
    PORT (web, padrão 8080)   P2P_PORT (padrão 5000)   DATA_DIR (padrão ./dados)
    PEERS="ip:porta,ip:porta"            TERACOIN_PRIVKEY (chave privada em hex)

Recursos (como no Bitcoin): assinaturas ECDSA secp256k1, prova de trabalho com
alvo (target), raiz de Merkle, ajuste de dificuldade a cada N blocos, recompensa
com halving, taxas, validação completa e regra da cadeia com mais trabalho.
Diferença principal: usa modelo de contas (saldo + nonce) em vez de UTXO.
Nota: a criptografia é implementada em Python puro e ainda não foi auditada.
"""
import argparse
import hashlib
import html
import json
import os
import re
import secrets
import socket
import socketserver
import sys
import threading
import time
from decimal import Decimal, InvalidOperation
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib import error as urlerror
from urllib import parse as urlparse
from urllib import request as urlrequest


# ============================ PARÂMETROS DA REDE ============================
def _env_int(nome, padrao):
    try:
        return int(os.getenv(nome, str(padrao)))
    except ValueError:
        return padrao


PORTA_HTTP = _env_int("PORT", 8080)
PORTA_P2P = _env_int("P2P_PORT", 5000)
PASTA_DADOS = os.getenv("DATA_DIR", "dados")

# Regras de consenso (todos os nós da rede precisam usar os mesmos valores)
NOME_REDE = "teracoin-mainnet"
VERSAO = 1
UNIDADE = 10 ** 8                           # 1 TRC = 100.000.000 unidades
RECOMPENSA_INICIAL = 50 * UNIDADE
INTERVALO_HALVING = _env_int("TRC_HALVING", 210_000)
TEMPO_BLOCO = _env_int("TRC_TEMPO_BLOCO", 120)        # segundos por bloco
INTERVALO_AJUSTE = max(2, _env_int("TRC_INTERVALO", 10))  # blocos entre ajustes
BITS_INICIAL = _env_int("TRC_BITS_INICIAL", 20)       # ~1 milhão de hashes
ALVO_INICIAL = (1 << (256 - BITS_INICIAL)) - 1        # também é o alvo máximo
GENESIS_TEMPO = 1767225600                            # 2026-01-01 00:00 UTC

# Limites de segurança (não são consenso)
MAX_TX_BLOCO = 500
MAX_MEMPOOL = 5000
MAX_FUTURO = 2 * 3600
MAX_MSG = 32 * 1024 * 1024
MAX_POST = 100 * 1024
MAX_PEERS = 32
MAX_VALOR = 2 ** 63


def log(msg):
    print(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] {msg}", flush=True)


def sha256d(dados):
    return hashlib.sha256(hashlib.sha256(dados).digest()).digest()


def formatar_trc(unidades):
    return f"{Decimal(unidades) / UNIDADE:.8f}"


def subsidio(altura):
    """Recompensa do bloco, cai pela metade a cada INTERVALO_HALVING blocos."""
    h = altura // INTERVALO_HALVING
    return 0 if h >= 64 else RECOMPENSA_INICIAL >> h


# ===================== CRIPTOGRAFIA: ECDSA secp256k1 =====================
_P = 2 ** 256 - 2 ** 32 - 977
_N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
_G = (0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
      0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)


def _somar(a, b):
    if a is None:
        return b
    if b is None:
        return a
    x1, y1 = a
    x2, y2 = b
    if x1 == x2 and (y1 + y2) % _P == 0:
        return None
    if a == b:
        m = 3 * x1 * x1 * pow(2 * y1, -1, _P) % _P
    else:
        m = (y2 - y1) * pow(x2 - x1, -1, _P) % _P
    x3 = (m * m - x1 - x2) % _P
    return (x3, (m * (x1 - x3) - y1) % _P)


def _mult(k, ponto):
    r = None
    while k:
        if k & 1:
            r = _somar(r, ponto)
        ponto = _somar(ponto, ponto)
        k >>= 1
    return r


def _comprimir(ponto):
    return ("02" if ponto[1] % 2 == 0 else "03") + f"{ponto[0]:064x}"


def _descomprimir(pub_hex):
    if not re.fullmatch(r"0[23][0-9a-f]{64}", pub_hex):
        raise ValueError("chave pública inválida")
    x = int(pub_hex[2:], 16)
    if x >= _P:
        raise ValueError("chave pública inválida")
    y2 = (pow(x, 3, _P) + 7) % _P
    y = pow(y2, (_P + 1) // 4, _P)
    if y * y % _P != y2:
        raise ValueError("ponto fora da curva")
    if (y % 2 == 0) != (pub_hex[1] == "2"):
        y = _P - y
    return (x, y)


def assinar(priv, hash_bytes):
    z = int.from_bytes(hash_bytes, "big")
    while True:
        k = secrets.randbelow(_N - 1) + 1
        r = _mult(k, _G)[0] % _N
        if r == 0:
            continue
        s = pow(k, -1, _N) * (z + r * priv) % _N
        if s == 0:
            continue
        if s > _N // 2:          # "low-s": evita assinatura maleável
            s = _N - s
        return f"{r:064x}{s:064x}"


def verificar(pub_hex, hash_bytes, assinatura_hex):
    try:
        pub = _descomprimir(pub_hex)
        r = int(assinatura_hex[:64], 16)
        s = int(assinatura_hex[64:], 16)
        if not (1 <= r < _N and 1 <= s <= _N // 2):
            return False
        z = int.from_bytes(hash_bytes, "big")
        w = pow(s, -1, _N)
        ponto = _somar(_mult(z * w % _N, _G), _mult(r * w % _N, pub))
        return ponto is not None and ponto[0] % _N == r
    except (ValueError, TypeError):
        return False


def endereco_de(pub_hex):
    return "T" + sha256d(bytes.fromhex(pub_hex))[:20].hex()


RE_END = r"T[0-9a-f]{40}"
RE_HEX64 = r"[0-9a-f]{64}"


class Carteira:
    def __init__(self, priv):
        if not 1 <= priv < _N:
            raise ValueError("chave privada inválida")
        self.priv = priv
        self.pub = _comprimir(_mult(priv, _G))
        self.endereco = endereco_de(self.pub)

    @staticmethod
    def carregar(pasta):
        env = os.getenv("TERACOIN_PRIVKEY", "").strip()
        if env:
            return Carteira(int(env, 16))
        os.makedirs(pasta, exist_ok=True)
        caminho = os.path.join(pasta, "carteira.json")
        if os.path.exists(caminho):
            with open(caminho, encoding="utf-8") as f:
                return Carteira(int(json.load(f)["chave_privada"], 16))
        c = Carteira(secrets.randbelow(_N - 1) + 1)
        with open(caminho, "w", encoding="utf-8") as f:
            json.dump({"chave_privada": f"{c.priv:064x}", "endereco": c.endereco}, f)
        try:
            os.chmod(caminho, 0o600)
        except OSError:
            pass
        log(f"🔑 Nova carteira criada em {caminho} — FAÇA BACKUP desse arquivo!")
        return c


# ============================ TRANSAÇÃO E BLOCO ============================
class Transacao:
    """pub vazio = transação coinbase (recompensa do minerador)."""

    def __init__(self, pub, destinatario, valor, taxa, nonce, assinatura=""):
        self.pub = pub
        self.destinatario = destinatario
        self.valor = valor
        self.taxa = taxa
        self.nonce = nonce
        self.assinatura = assinatura

    @property
    def eh_coinbase(self):
        return self.pub == ""

    @property
    def remetente(self):
        return "COINBASE" if self.eh_coinbase else endereco_de(self.pub)

    def _corpo(self):
        return json.dumps({"rede": NOME_REDE, "pub": self.pub, "para": self.destinatario,
                           "valor": self.valor, "taxa": self.taxa, "nonce": self.nonce},
                          sort_keys=True, separators=(",", ":")).encode()

    def id(self):
        return sha256d(self._corpo()).hex()

    def assinar(self, carteira):
        self.assinatura = assinar(carteira.priv, bytes.fromhex(self.id()))

    def assinatura_valida(self):
        return verificar(self.pub, bytes.fromhex(self.id()), self.assinatura)

    def validar_forma(self):
        for v in (self.valor, self.taxa, self.nonce):
            if type(v) is not int or v < 0 or v > MAX_VALOR:
                raise ValueError("número inválido na transação")
        if not isinstance(self.destinatario, str) or not re.fullmatch(RE_END, self.destinatario):
            raise ValueError("endereço de destino inválido")
        if not isinstance(self.pub, str) or not isinstance(self.assinatura, str):
            raise ValueError("transação malformada")
        if self.eh_coinbase:
            if self.assinatura != "" or self.taxa != 0:
                raise ValueError("coinbase malformada")
        else:
            if not re.fullmatch(r"0[23][0-9a-f]{64}", self.pub):
                raise ValueError("chave pública inválida")
            if not re.fullmatch(r"[0-9a-f]{128}", self.assinatura):
                raise ValueError("assinatura malformada")
            if self.valor <= 0:
                raise ValueError("valor deve ser positivo")

    def para_dict(self):
        return {"pub": self.pub, "para": self.destinatario, "valor": self.valor,
                "taxa": self.taxa, "nonce": self.nonce, "assinatura": self.assinatura}

    @staticmethod
    def de_dict(d):
        try:
            tx = Transacao(d["pub"], d["para"], d["valor"], d["taxa"], d["nonce"], d["assinatura"])
        except (KeyError, TypeError):
            raise ValueError("transação malformada")
        tx.validar_forma()
        return tx


def raiz_merkle(ids_hex):
    if not ids_hex:
        return "0" * 64
    nivel = [bytes.fromhex(i) for i in ids_hex]
    while len(nivel) > 1:
        if len(nivel) % 2:
            nivel.append(nivel[-1])
        nivel = [sha256d(nivel[i] + nivel[i + 1]) for i in range(0, len(nivel), 2)]
    return nivel[0].hex()


class Bloco:
    def __init__(self, indice, hash_anterior, transacoes, timestamp, alvo, nonce=0, hash_=""):
        self.indice = indice
        self.hash_anterior = hash_anterior
        self.transacoes = transacoes
        self.timestamp = timestamp
        self.alvo = alvo
        self.nonce = nonce
        self.hash = hash_
        self.merkle = raiz_merkle([t.id() for t in transacoes])

    def _prefixo(self):
        return (f"{VERSAO}|{self.indice}|{self.hash_anterior}|{self.merkle}|"
                f"{self.timestamp}|{self.alvo:064x}|")

    def calcular_hash(self):
        return sha256d((self._prefixo() + str(self.nonce)).encode()).hex()

    def minerar(self, cancelar):
        """Procura um nonce cujo hash seja <= alvo. Retorna False se cancelado."""
        prefixo = self._prefixo().encode()
        sha = hashlib.sha256
        alvo = self.alvo
        n = 0
        while True:
            d = sha(sha(prefixo + str(n).encode()).digest()).digest()
            if int.from_bytes(d, "big") <= alvo:
                self.nonce = n
                self.hash = d.hex()
                return True
            n += 1
            if n & 0x3FFF == 0 and cancelar():
                return False

    def trabalho(self):
        return (1 << 256) // (self.alvo + 1)

    def para_dict(self):
        return {"indice": self.indice, "hash_anterior": self.hash_anterior,
                "merkle": self.merkle, "timestamp": self.timestamp,
                "alvo": f"{self.alvo:064x}", "nonce": self.nonce, "hash": self.hash,
                "transacoes": [t.para_dict() for t in self.transacoes]}

    @staticmethod
    def de_dict(d):
        try:
            if not isinstance(d["transacoes"], list) or len(d["transacoes"]) > MAX_TX_BLOCO + 1:
                raise ValueError("lista de transações inválida")
            for v in (d["indice"], d["timestamp"], d["nonce"]):
                if type(v) is not int or v < 0 or v > MAX_VALOR:
                    raise ValueError("campo numérico inválido")
            for h in (d["hash_anterior"], d["alvo"], d["hash"]):
                if not isinstance(h, str) or not re.fullmatch(RE_HEX64, h):
                    raise ValueError("campo hexadecimal inválido")
            txs = [Transacao.de_dict(t) for t in d["transacoes"]]
            return Bloco(d["indice"], d["hash_anterior"], txs, d["timestamp"],
                         int(d["alvo"], 16), d["nonce"], d["hash"])
        except (KeyError, TypeError):
            raise ValueError("bloco malformado")


def criar_genesis():
    g = Bloco(0, "0" * 64, [], GENESIS_TEMPO, ALVO_INICIAL)
    g.hash = g.calcular_hash()
    return g


GENESIS = criar_genesis()


# =========================== ESTADO E VALIDAÇÃO ===========================
class Estado:
    def __init__(self):
        self.saldos = {}
        self.nonces = {}

    def saldo(self, endereco):
        return self.saldos.get(endereco, 0)

    def copiar(self):
        e = Estado()
        e.saldos = dict(self.saldos)
        e.nonces = dict(self.nonces)
        return e


def aplicar_tx(estado, tx):
    rem = tx.remetente
    if estado.nonces.get(rem, 0) != tx.nonce:
        raise ValueError("nonce inválido (possível repetição)")
    custo = tx.valor + tx.taxa
    if estado.saldo(rem) < custo:
        raise ValueError("saldo insuficiente")
    estado.saldos[rem] = estado.saldo(rem) - custo
    estado.saldos[tx.destinatario] = estado.saldo(tx.destinatario) + tx.valor
    estado.nonces[rem] = tx.nonce + 1


def alvo_esperado(blocos):
    """Alvo exigido para o próximo bloco (ajuste estilo Bitcoin, limite de 4x)."""
    altura = len(blocos)
    ant = blocos[-1]
    if altura % INTERVALO_AJUSTE != 0:
        return ant.alvo
    primeiro = blocos[altura - INTERVALO_AJUSTE]
    esperado = TEMPO_BLOCO * (INTERVALO_AJUSTE - 1)
    real = max(esperado // 4, min(esperado * 4, ant.timestamp - primeiro.timestamp))
    return max(1, min(ant.alvo * real // esperado, ALVO_INICIAL))


def validar_bloco(blocos, bloco, estado, agora):
    """Valida o bloco sobre 'blocos' e aplica no 'estado'. Levanta ValueError."""
    ant = blocos[-1]
    altura = len(blocos)
    if bloco.indice != altura:
        raise ValueError("índice errado")
    if bloco.hash_anterior != ant.hash:
        raise ValueError("não encaixa no bloco anterior")
    if bloco.hash != bloco.calcular_hash():
        raise ValueError("hash não confere")
    if bloco.alvo != alvo_esperado(blocos):
        raise ValueError("dificuldade incorreta")
    if int(bloco.hash, 16) > bloco.alvo:
        raise ValueError("prova de trabalho insuficiente")
    if not (ant.timestamp < bloco.timestamp <= agora + MAX_FUTURO):
        raise ValueError("timestamp inválido")
    txs = bloco.transacoes
    if not 1 <= len(txs) <= MAX_TX_BLOCO + 1:
        raise ValueError("quantidade de transações inválida")
    if len({t.id() for t in txs}) != len(txs):
        raise ValueError("transações repetidas")
    cb = txs[0]
    if not cb.eh_coinbase or cb.nonce != altura or any(t.eh_coinbase for t in txs[1:]):
        raise ValueError("coinbase inválida")
    taxas = 0
    for tx in txs[1:]:
        if not tx.assinatura_valida():
            raise ValueError("assinatura inválida")
        aplicar_tx(estado, tx)
        taxas += tx.taxa
    if cb.valor > subsidio(altura) + taxas:
        raise ValueError("recompensa acima do permitido")
    estado.saldos[cb.destinatario] = estado.saldo(cb.destinatario) + cb.valor


def validar_cadeia(dados):
    """Revalida uma cadeia inteira a partir da gênese. Retorna (blocos, estado)."""
    if not isinstance(dados, list) or not dados:
        raise ValueError("cadeia vazia")
    blocos = [Bloco.de_dict(d) for d in dados]
    g = blocos[0]
    if g.hash != GENESIS.hash or g.calcular_hash() != g.hash or g.transacoes:
        raise ValueError("bloco gênese diferente")
    estado = Estado()
    cadeia = [g]
    agora = time.time()
    for b in blocos[1:]:
        validar_bloco(cadeia, b, estado, agora)
        cadeia.append(b)
    return cadeia, estado


# ================================ BLOCKCHAIN ================================
class Blockchain:
    def __init__(self, pasta):
        self.pasta = pasta
        self.lock = threading.RLock()
        self.blocos = [GENESIS]
        self.hashes = {GENESIS.hash}
        self.estado = Estado()
        self.mempool = {}
        self._carregar()

    # --- persistência ---
    def _caminho(self):
        return os.path.join(self.pasta, "cadeia.json")

    def _carregar(self):
        caminho = self._caminho()
        if not os.path.exists(caminho):
            return
        try:
            with open(caminho, encoding="utf-8") as f:
                blocos, estado = validar_cadeia(json.load(f))
            self.blocos, self.estado = blocos, estado
            self.hashes = {b.hash for b in blocos}
            log(f"💾 Cadeia carregada do disco: {len(blocos)} blocos")
        except (ValueError, OSError) as e:
            log(f"⚠️ Cadeia salva é inválida ({e}); movida para .corrompida")
            try:
                os.replace(caminho, caminho + ".corrompida")
            except OSError:
                pass

    def _salvar(self):
        try:
            os.makedirs(self.pasta, exist_ok=True)
            tmp = self._caminho() + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump([b.para_dict() for b in self.blocos], f)
            os.replace(tmp, self._caminho())
        except OSError as e:
            log(f"⚠️ Não foi possível salvar a cadeia: {e}")

    # --- consultas ---
    def ponta(self):
        with self.lock:
            return self.blocos[-1].hash

    def trabalho(self):
        with self.lock:
            return sum(b.trabalho() for b in self.blocos)

    def exportar(self):
        with self.lock:
            return [b.para_dict() for b in self.blocos]

    def ultimos(self, n):
        with self.lock:
            return list(self.blocos[-n:])

    def conta(self, endereco):
        with self.lock:
            pend = [t for t in self.mempool.values() if t.remetente == endereco]
            return {"saldo": self.estado.saldo(endereco),
                    "proximo_nonce": self.estado.nonces.get(endereco, 0) + len(pend)}

    # --- mempool ---
    def adicionar_tx(self, tx):
        if tx.eh_coinbase:
            raise ValueError("coinbase não entra na mempool")
        if not tx.assinatura_valida():
            raise ValueError("assinatura inválida")
        with self.lock:
            txid = tx.id()
            if txid in self.mempool:
                return False
            if len(self.mempool) >= MAX_MEMPOOL:
                raise ValueError("mempool cheia")
            rem = tx.remetente
            pend = [t for t in self.mempool.values() if t.remetente == rem]
            if tx.nonce != self.estado.nonces.get(rem, 0) + len(pend):
                raise ValueError("nonce inválido")
            gasto = sum(t.valor + t.taxa for t in pend) + tx.valor + tx.taxa
            if self.estado.saldo(rem) < gasto:
                raise ValueError("saldo insuficiente")
            self.mempool[txid] = tx
            return True

    def _limpar_mempool(self):
        est = self.estado.copiar()
        novo = {}
        for txid, tx in sorted(self.mempool.items(), key=lambda kv: kv[1].nonce):
            try:
                aplicar_tx(est, tx)
                novo[txid] = tx
            except ValueError:
                pass
        self.mempool = novo

    # --- blocos ---
    def montar_candidato(self, destino):
        with self.lock:
            altura = len(self.blocos)
            ant = self.blocos[-1]
            est = self.estado.copiar()
            escolhidas, taxas = [], 0
            for tx in sorted(self.mempool.values(), key=lambda t: (t.nonce, -t.taxa)):
                if len(escolhidas) >= MAX_TX_BLOCO:
                    break
                try:
                    aplicar_tx(est, tx)
                except ValueError:
                    continue
                escolhidas.append(tx)
                taxas += tx.taxa
            cb = Transacao("", destino, subsidio(altura) + taxas, 0, altura)
            ts = max(int(time.time()), ant.timestamp + 1)
            return Bloco(altura, ant.hash, [cb] + escolhidas, ts, alvo_esperado(self.blocos))

    def adicionar_bloco(self, bloco):
        """Retorna (status, motivo): ok | duplicado | desconectado | antigo | invalido."""
        with self.lock:
            if bloco.hash in self.hashes:
                return "duplicado", ""
            if bloco.hash_anterior != self.blocos[-1].hash:
                if bloco.indice >= len(self.blocos):
                    return "desconectado", ""
                return "antigo", ""
            try:
                est = self.estado.copiar()
                validar_bloco(self.blocos, bloco, est, time.time())
            except ValueError as e:
                return "invalido", str(e)
            self.blocos.append(bloco)
            self.hashes.add(bloco.hash)
            self.estado = est
            self._limpar_mempool()
            self._salvar()
            return "ok", ""

    def tentar_substituir(self, dados):
        """Troca a cadeia local por outra válida com mais trabalho acumulado."""
        novos, estado = validar_cadeia(dados)
        with self.lock:
            if sum(b.trabalho() for b in novos) <= self.trabalho():
                return False
            self.blocos, self.estado = novos, estado
            self.hashes = {b.hash for b in novos}
            self._limpar_mempool()
            self._salvar()
            return True


# ================================ REDE P2P ================================
def _ler_exato(sock, n):
    buf = bytearray()
    while len(buf) < n:
        parte = sock.recv(min(65536, n - len(buf)))
        if not parte:
            raise ConnectionError("conexão fechada")
        buf += parte
    return bytes(buf)


def enviar_msg(sock, obj):
    dados = json.dumps(obj, separators=(",", ":")).encode()
    sock.sendall(len(dados).to_bytes(4, "big") + dados)


def receber_msg(sock):
    tamanho = int.from_bytes(_ler_exato(sock, 4), "big")
    if tamanho > MAX_MSG:
        raise ValueError("mensagem grande demais")
    msg = json.loads(_ler_exato(sock, tamanho))
    if not isinstance(msg, dict):
        raise ValueError("mensagem inválida")
    return msg


class No:
    def __init__(self, chain, carteira, peers):
        self.chain = chain
        self.carteira = carteira
        self.peers = set(peers)
        self.peers_lock = threading.Lock()
        self.minerando = False

    # --- peers ---
    def adicionar_peer(self, peer):
        ip, porta = peer
        if porta == PORTA_P2P and ip in ("127.0.0.1", "::1", "localhost"):
            return
        with self.peers_lock:
            if len(self.peers) < MAX_PEERS:
                self.peers.add(peer)

    def lista_peers(self):
        with self.peers_lock:
            return list(self.peers)

    def broadcast(self, msg, excluir=None):
        msg = dict(msg, porta=PORTA_P2P)
        for peer in self.lista_peers():
            if peer != excluir:
                threading.Thread(target=self._enviar, args=(peer, msg), daemon=True).start()

    def _enviar(self, peer, msg):
        try:
            with socket.create_connection(peer, timeout=5) as s:
                enviar_msg(s, msg)
        except OSError as e:
            log(f"[P2P] falha ao enviar para {peer[0]}:{peer[1]}: {e}")

    def _pedir(self, peer, msg):
        with socket.create_connection(peer, timeout=10) as s:
            s.settimeout(30)
            enviar_msg(s, dict(msg, porta=PORTA_P2P))
            return receber_msg(s)

    def sincronizar_com(self, peer):
        try:
            st = self._pedir(peer, {"tipo": "status"})
            if int(st["trabalho"]) <= self.chain.trabalho():
                return
            resp = self._pedir(peer, {"tipo": "get_chain"})
            if self.chain.tentar_substituir(resp["blocos"]):
                with self.chain.lock:
                    ultimo = self.chain.blocos[-1]
                log(f"🔄 Cadeia sincronizada com {peer[0]}:{peer[1]} — altura {ultimo.indice}")
                self.broadcast({"tipo": "bloco", "bloco": ultimo.para_dict()}, excluir=peer)
        except (OSError, ValueError, KeyError, TypeError) as e:
            log(f"[P2P] sincronização com {peer[0]}:{peer[1]} falhou: {e}")

    def loop_sincronizacao(self):
        while True:
            for peer in self.lista_peers():
                self.sincronizar_com(peer)
            time.sleep(60)

    # --- recebimento ---
    def receber_bloco(self, d, origem):
        try:
            bloco = Bloco.de_dict(d)
        except ValueError as e:
            log(f"[P2P] bloco rejeitado: {e}")
            return
        status, motivo = self.chain.adicionar_bloco(bloco)
        if status == "ok":
            log(f"📦 Bloco #{bloco.indice} recebido da rede — {bloco.hash[:16]}…")
            self.broadcast({"tipo": "bloco", "bloco": d}, excluir=origem)
        elif status == "desconectado" and origem:
            threading.Thread(target=self.sincronizar_com, args=(origem,), daemon=True).start()
        elif status == "invalido":
            log(f"[P2P] bloco inválido rejeitado: {motivo}")

    def receber_tx(self, d, origem=None):
        tx = Transacao.de_dict(d)
        if self.chain.adicionar_tx(tx):
            log(f"💸 Nova transação {tx.id()[:16]}…: {formatar_trc(tx.valor)} TRC")
            self.broadcast({"tipo": "tx", "tx": d}, excluir=origem)
            return tx.id()
        return tx.id()

    # --- mineração ---
    def loop_mineracao(self):
        self.minerando = True
        log(f"⛏️ Mineração ativa. Recompensas vão para {self.carteira.endereco}")
        while True:
            bloco = self.chain.montar_candidato(self.carteira.endereco)
            base = bloco.hash_anterior
            inicio = time.time()
            if not bloco.minerar(lambda: self.chain.ponta() != base):
                continue
            status, motivo = self.chain.adicionar_bloco(bloco)
            if status == "ok":
                dur = time.time() - inicio
                with self.chain.lock:
                    saldo = self.chain.estado.saldo(self.carteira.endereco)
                log(f"✅ Bloco #{bloco.indice} minerado! Hash: {bloco.hash}")
                log(f"   Nonce: {bloco.nonce} | Tempo: {dur:.2f}s | "
                    f"Saldo: {formatar_trc(saldo)} TRC")
                self.broadcast({"tipo": "bloco", "bloco": bloco.para_dict()})
            elif status == "invalido":
                log(f"⚠️ Bloco minerado foi rejeitado: {motivo}")

    def status(self):
        c = self.chain
        with c.lock:
            ult = c.blocos[-1]
            return {"altura": ult.indice, "ponta": ult.hash,
                    "alvo": f"{ult.alvo:064x}",
                    "dificuldade": round(ALVO_INICIAL / ult.alvo, 4),
                    "hashes_por_bloco": (1 << 256) // (ult.alvo + 1),
                    "recompensa": formatar_trc(subsidio(ult.indice + 1)),
                    "mempool": len(c.mempool), "peers": len(self.lista_peers()),
                    "minerando": self.minerando, "endereco": self.carteira.endereco,
                    "saldo": formatar_trc(c.estado.saldo(self.carteira.endereco)),
                    "trabalho": str(c.trabalho())}


class ManipuladorP2P(socketserver.BaseRequestHandler):
    def handle(self):
        no = self.server.no
        try:
            self.request.settimeout(10)
            msg = receber_msg(self.request)
            ip = self.client_address[0]
            porta = msg.get("porta")
            origem = None
            if type(porta) is int and 1 <= porta <= 65535:
                origem = (ip, porta)
                no.adicionar_peer(origem)
            tipo = msg.get("tipo")
            if tipo == "status":
                enviar_msg(self.request, {"tipo": "status", "trabalho": str(no.chain.trabalho()),
                                          "altura": no.chain.blocos[-1].indice})
            elif tipo == "get_chain":
                enviar_msg(self.request, {"tipo": "chain", "blocos": no.chain.exportar()})
            elif tipo == "bloco":
                no.receber_bloco(msg.get("bloco"), origem)
            elif tipo == "tx":
                try:
                    no.receber_tx(msg.get("tx"), origem)
                except ValueError as e:
                    log(f"[P2P] transação rejeitada: {e}")
        except (OSError, ValueError, TypeError) as e:
            log(f"[P2P] conexão descartada: {e}")


class ServidorP2P(socketserver.ThreadingTCPServer):
    allow_reuse_address = True
    daemon_threads = True


# ================================ SERVIDOR WEB ================================
def pagina_html(no):
    st = no.status()
    linhas = "".join(
        f"<tr><td>{b.indice}</td><td>{time.strftime('%H:%M:%S', time.gmtime(b.timestamp))}</td>"
        f"<td>{len(b.transacoes)}</td><td title='{b.hash}'>{b.hash[:20]}…</td></tr>"
        for b in reversed(no.chain.ultimos(10)))
    return f"""<!doctype html><html><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta http-equiv="refresh" content="15"><title>Teracoin — Nó</title></head>
<body style="background:#111;color:#fff;padding:24px;font-family:Arial,sans-serif">
<h1>⛏️ TERACOIN (TRC)</h1>
<h2>Saldo do nó: <span style="color:#0f0">{html.escape(st['saldo'])} TRC</span></h2>
<p>Carteira: <code>{html.escape(st['endereco'])}</code></p>
<p>Altura: {st['altura']} | Dificuldade: {st['dificuldade']} |
Recompensa: {html.escape(st['recompensa'])} TRC</p>
<p>Mempool: {st['mempool']} | Peers: {st['peers']} |
Minerando: {'sim' if st['minerando'] else 'não'}</p>
<table style="border-collapse:collapse;width:100%;max-width:640px" border="1" cellpadding="6">
<tr><th>#</th><th>Hora (UTC)</th><th>Txs</th><th>Hash</th></tr>{linhas}</table>
</body></html>"""


class ManipuladorHTTP(BaseHTTPRequestHandler):
    server_version = "Teracoin"

    def log_message(self, *args):
        pass

    def _responder(self, codigo, corpo, tipo="application/json"):
        dados = corpo if isinstance(corpo, bytes) else json.dumps(corpo).encode()
        self.send_response(codigo)
        self.send_header("Content-Type", f"{tipo}; charset=utf-8")
        self.send_header("Content-Length", str(len(dados)))
        self.end_headers()
        self.wfile.write(dados)

    def do_GET(self):
        no = self.server.no
        url = urlparse.urlparse(self.path)
        caminho = url.path
        if caminho == "/":
            self._responder(200, pagina_html(no).encode(), "text/html")
        elif caminho == "/api/status":
            self._responder(200, no.status())
        elif caminho == "/api/blocos":
            try:
                n = int(urlparse.parse_qs(url.query).get("n", ["10"])[0])
            except ValueError:
                n = 10
            n = max(1, min(n, 100))
            self._responder(200, [b.para_dict() for b in no.chain.ultimos(n)])
        elif caminho.startswith("/api/conta/"):
            end = caminho[len("/api/conta/"):]
            if not re.fullmatch(RE_END, end):
                self._responder(400, {"erro": "endereço inválido"})
            else:
                info = no.chain.conta(end)
                info["saldo_trc"] = formatar_trc(info["saldo"])
                self._responder(200, info)
        else:
            self._responder(404, {"erro": "não encontrado"})

    def do_POST(self):
        no = self.server.no
        if self.path != "/api/tx":
            return self._responder(404, {"erro": "não encontrado"})
        try:
            n = int(self.headers.get("Content-Length", "0"))
            if not 0 < n <= MAX_POST:
                raise ValueError("tamanho inválido")
            d = json.loads(self.rfile.read(n))
            txid = no.receber_tx(d)
            self._responder(200, {"ok": True, "id": txid})
        except ValueError as e:
            self._responder(400, {"ok": False, "erro": str(e)})


# ===================================== CLI =====================================
def _parse_trc(texto, permitir_zero=False):
    try:
        v = Decimal(texto) * UNIDADE
    except InvalidOperation:
        raise SystemExit(f"Valor inválido: {texto}")
    if v != v.to_integral_value() or v < 0 or (v == 0 and not permitir_zero):
        raise SystemExit(f"Valor inválido (até 8 casas decimais, positivo): {texto}")
    return int(v)


def _http_json(url, dados=None):
    req = urlrequest.Request(url, data=None if dados is None else json.dumps(dados).encode(),
                             headers={"Content-Type": "application/json"})
    try:
        with urlrequest.urlopen(req, timeout=15) as r:
            return json.loads(r.read())
    except urlerror.HTTPError as e:
        corpo = e.read().decode(errors="replace")
        raise SystemExit(f"Erro do nó ({e.code}): {corpo}")
    except urlerror.URLError as e:
        raise SystemExit(f"Não consegui falar com o nó em {url}: {e.reason}")


def _parse_peers(texto):
    peers = []
    for item in filter(None, (p.strip() for p in texto.split(","))):
        ip, _, porta = item.rpartition(":") if ":" in item else (item, "", str(PORTA_P2P))
        try:
            peers.append((ip, int(porta)))
        except ValueError:
            log(f"⚠️ Peer ignorado: {item}")
    return peers


def cmd_rodar(args):
    carteira = Carteira.carregar(PASTA_DADOS)
    chain = Blockchain(PASTA_DADOS)
    no = No(chain, carteira, _parse_peers(args.peers))

    p2p = ServidorP2P(("0.0.0.0", PORTA_P2P), ManipuladorP2P)
    p2p.no = no
    web = ThreadingHTTPServer(("0.0.0.0", PORTA_HTTP), ManipuladorHTTP)
    web.no = no
    threading.Thread(target=p2p.serve_forever, daemon=True).start()
    threading.Thread(target=web.serve_forever, daemon=True).start()
    log(f"🌐 Web na porta {PORTA_HTTP} | P2P na porta {PORTA_P2P} | "
        f"{len(chain.blocos)} blocos | dificuldade inicial {BITS_INICIAL} bits")
    log(f"👛 Carteira do nó: {carteira.endereco}")

    threading.Thread(target=no.loop_sincronizacao, daemon=True).start()
    if not args.sem_minerar:
        threading.Thread(target=no.loop_mineracao, daemon=True).start()
    try:
        while True:
            time.sleep(1)
    except KeyboardInterrupt:
        log("Encerrando…")


def cmd_carteira(_args):
    c = Carteira.carregar(PASTA_DADOS)
    print(f"Endereço: {c.endereco}\nChave pública: {c.pub}")


def cmd_enviar(args):
    if not re.fullmatch(RE_END, args.destino):
        raise SystemExit("Endereço de destino inválido (formato: T + 40 caracteres hex).")
    c = Carteira.carregar(PASTA_DADOS)
    valor = _parse_trc(args.valor)
    taxa = _parse_trc(args.taxa, permitir_zero=True)
    info = _http_json(f"{args.url}/api/conta/{c.endereco}")
    if info["saldo"] < valor + taxa:
        raise SystemExit(f"Saldo insuficiente: {formatar_trc(info['saldo'])} TRC")
    tx = Transacao(c.pub, args.destino, valor, taxa, info["proximo_nonce"])
    tx.assinar(c)
    resp = _http_json(f"{args.url}/api/tx", tx.para_dict())
    print(f"Transação enviada: {resp['id']}")


def principal():
    ap = argparse.ArgumentParser(prog="main.py", description="Teracoin (TRC) — blockchain própria")
    sub = ap.add_subparsers(dest="cmd")
    p = sub.add_parser("rodar", help="roda o nó")
    p.add_argument("--sem-minerar", action="store_true")
    p.add_argument("--peers", default=os.getenv("PEERS", ""), help="ip:porta,ip:porta")
    p.set_defaults(func=cmd_rodar)
    sub.add_parser("carteira", help="mostra sua carteira").set_defaults(func=cmd_carteira)
    p = sub.add_parser("enviar", help="envia TRC")
    p.add_argument("destino")
    p.add_argument("valor")
    p.add_argument("--taxa", default="0.0001")
    p.add_argument("--url", default=f"http://127.0.0.1:{PORTA_HTTP}", help="URL web do nó")
    p.set_defaults(func=cmd_enviar)
    args = ap.parse_args(sys.argv[1:] or ["rodar"])
    args.func(args)


if __name__ == "__main__":
    principal()
