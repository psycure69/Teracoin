import hashlib
import json
import time
import os
import threading
import socket
import pickle
from http.server import HTTPServer, SimpleHTTPRequestHandler
from collections import OrderedDict

PORTA_LOCAL = int(os.getenv("PORT", 8080))
PORTA_P2P = 5000
PEERS = []

def log(mensagem):
    print(f"[{time.ctime()}] {mensagem}")

class Transacao:
    def __init__(self, remetente, destinatario, valor, assinatura=""):
        self.remetente = remetente
        self.destinatario = destinatario
        self.valor = valor
        self.assinatura = assinatura
        self.tempo = time.time()

    def para_dict(self):
        return OrderedDict({
            "remetente": self.remetente,
            "destinatario": self.destinatario,
            "valor": self.valor,
            "assinatura": self.assinatura,
            "tempo": self.tempo
        })

    def gerar_hash(self):
        return hashlib.sha256(json.dumps(self.para_dict(), sort_keys=True).encode()).hexdigest()

class Bloco:
    def __init__(self, indice, transacoes, hash_anterior):
        self.indice = indice
        self.transacoes = transacoes
        self.hash_anterior = hash_anterior
        self.nonce = 0
        self.tempo = time.time()
        self.hash = ""

    def calcular_hash(self):
        return hashlib.sha256(f"{self.indice}{self.transacoes}{self.hash_anterior}{self.nonce}{self.tempo}".encode()).hexdigest()

    def minerar(self, dificuldade):
        alvo = "0" * dificuldade
        while self.calcular_hash()[:dificuldade] != alvo:
            self.nonce += 1
        self.hash = self.calcular_hash()

class Blockchain:
    def __init__(self, dificuldade=6, recompensa=50.0):
        self.cadeia = []
        self.transacoes_pendentes = []
        self.dificuldade = dificuldade
        self.recompensa = recompensa
        self.criar_bloco_genese()

    def criar_bloco_genese(self):
        bloco = Bloco(0, [], "0")
        bloco.minerar(self.dificuldade)
        self.cadeia.append(bloco)

    def ultimo_bloco(self):
        return self.cadeia[-1]

    def adicionar_transacao(self, tx):
        self.transacoes_pendentes.append(tx)

    def obter_saldo(self, endereco):
        saldo = 0.0
        for bloco in self.cadeia:
            for tx in bloco.transacoes:
                if tx.destinatario == endereco:
                    saldo += tx.valor
                if tx.remetente == endereco:
                    saldo -= tx.valor
        return saldo

    def minerar_bloco_pendente(self, endereco_minerador):
        tx_recompensa = Transacao("SISTEMA", endereco_minerador, self.recompensa)
        todas_tx = [tx_recompensa] + self.transacoes_pendentes
        novo_bloco = Bloco(len(self.cadeia), todas_tx, self.ultimo_bloco().hash)

        inicio = time.time()
        novo_bloco.minerar(self.dificuldade)
        tempo_gasto = time.time() - inicio

        self.cadeia.append(novo_bloco)
        self.transacoes_pendentes = []
        return novo_bloco, tempo_gasto

    def cadeia_valida(self):
        anterior = self.cadeia[0]
        i = 1
        while i < len(self.cadeia):
            atual = self.cadeia[i]
            if atual.hash_anterior != anterior.hash:
                return False
            if atual.calcular_hash() != atual.hash:
                return False
            anterior = atual
            i += 1
        return True

TERACOIN = Blockchain(dificuldade=6, recompensa=50.0)
CARTEIRA_CRIADOR = "7d87d90f077cf4a5dc6a"

class ServidorWebSimples(SimpleHTTPRequestHandler):
    def do_GET(self):
        self.send_response(200)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.end_headers()
        saldo = TERACOIN.obter_saldo(CARTEIRA_CRIADOR)
        pagina = f"""
        <html>
        <head>
            <title>Teracoin — Carteira</title>
        </head>
        <body style="background:#111;color:#fff;padding:30px;font-family:Arial">
            <h1>⛏️ TERACOIN (TRC)</h1>
            <h2>Saldo: <span style="color:#0f0">{saldo:.2f} TRC</span></h2>
            <p>Blocos: {len(TERACOIN.cadeia)}</p>
            <p>Dificuldade: {TERACOIN.dificuldade}</p>
            <p>Carteira: {CARTEIRA_CRIADOR}</p>
        </body>
        </html>
        """
        self.wfile.write(pagina.encode("utf-8"))

def iniciar_servidor_web():
    try:
        servidor = HTTPServer(("0.0.0.0", PORTA_LOCAL), ServidorWebSimples)
        log(f"✅ Servidor Web na porta {PORTA_LOCAL}")
        servidor.serve_forever()
    except Exception as e:
        log(f"❌ Erro Web: {e}")

def iniciar_servidor_p2p():
    servidor = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    servidor.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    servidor.bind(("0.0.0.0", PORTA_P2P))
    servidor.listen(5)
    log(f"🌐 P2P escutando na porta {PORTA_P2P}")

    while True:
        try:
            conn, addr = servidor.accept()
            dados = conn.recv(8192)
            if dados:
                msg = pickle.loads(dados)
                if msg["tipo"] == "cadeia":
                    nova_cadeia = msg["cadeia"]
                    if len(nova_cadeia) > len(TERACOIN.cadeia) and TERACOIN.cadeia_valida():
                        TERACOIN.cadeia = nova_cadeia
                        log("[P2P] Cadeia atualizada!")
            conn.close()
        except Exception as e:
            log(f"[P2P Erro] {e}")

def transmitir_para_peers():
    dados = {
        "tipo": "cadeia",
        "cadeia": TERACOIN.cadeia
    }
    for ip in PEERS:
        try:
            s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            s.connect((ip, PORTA_P2P))
            s.send(pickle.dumps(dados))
            s.close()
        except Exception as e:
            log(f"[P2P Falha] {ip}: {e}")

def minerador_loop():
    global TERACOIN
    while True:
        log("\n⛏️ Minerando bloco...")
        bloco, tempo = TERACOIN.minerar_bloco_pendente(CARTEIRA_CRIADOR)

        # ✅ AJUSTE AUTOMÁTICO DE DIFICULDADE DE VOLTA
        if tempo < 120:
            TERACOIN.dificuldade += 1
            log(f"📈 Dificuldade subiu para {TERACOIN.dificuldade}")
        elif tempo > 180 and TERACOIN.dificuldade > 1:
            TERACOIN.dificuldade -= 1
            log(f"📉 Dificuldade desceu para {TERACOIN.dificuldade}")

        saldo = TERACOIN.obter_saldo(CARTEIRA_CRIADOR)
        log(f"✅ Bloco #{bloco.indice} minerado! Hash: {bloco.hash}")
        log(f"[Teracoin] Nonce: {bloco.nonce} | Tempo: {tempo:.2f}s")
        log(f"💰 Saldo Criador: {saldo:.2f} TRC")

        transmitir_para_peers()

if __name__ == "__main__":
    threading.Thread(target=iniciar_servidor_web, daemon=True).start()
    threading.Thread(target=iniciar_servidor_p2p, daemon=True).start()
    minerador_loop()
